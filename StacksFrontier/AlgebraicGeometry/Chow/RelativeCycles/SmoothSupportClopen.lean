module

public import Mathlib.Topology.LocallyConstant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksFrontier.Topology.Sober.SpecializationStableNeighborhood
public import StacksCore.Tactic.StacksAttribute

/-!
# Clopen supports of cycles invariant along specializations

Four ingredients towards the statement that the support of a relative `r`-cycle on a smooth
morphism of relative dimension `r` over a locally Noetherian base is open and closed in the
total space.

First, a subset of a quasi-sober locally Noetherian topological space which is stable under
specialization and under generalization is open and closed. Indeed each point has a Noetherian
open neighbourhood, which is quasi-sober and has finitely many irreducible components, and on
such a space a doubly stable subset is open; applying this to the subset and to its complement
gives both halves.

Second, the weight with which a point enters a flat pullback is one as soon as the
scheme-theoretic inverse image of the reduced closure of its image is reduced. This is the
computation that makes the fibrewise coefficient of a family of cycles invariant under base
change along a residue field extension when the fibre through the point is smooth: smoothness
makes the base-changed component reduced, and a reduced closed subscheme has multiplicity one
at every generic point of a component.

Third, on an integral scheme whose generic point is the only point of relative dimension `k`,
every `k`-cycle is an integer multiple of the fundamental cycle, so its support is either empty
or the whole space, according to whether its coefficient at the generic point vanishes. This is
the shape that the member `α_s = n[X_s]` of a relative cycle takes on an irreducible smooth
fibre.

Fourth, on a scheme smooth over a field the irreducible component through a point coincides
with its connected component and is open and closed. So that component is an open subscheme,
smooth over the field, and a point of a smooth fibre lies on exactly one component.

## Main results

* `Stacks.Chow.isOpen_of_specializes_iff`, `Stacks.Chow.isClopen_of_specializes_iff` — a subset
  whose membership is invariant along every specialization is open, and open and closed.
* `Stacks.Chow.flatPullbackWeight_eq_one_of_reduced` — the weight is one when the inverse image
  of the reduced closure of the image point is reduced.
* `Stacks.Chow.cycle_eq_smul_fundamentalCycle_of_unique_top_point` — a `k`-cycle on an integral
  scheme with a unique point of relative dimension `k` is a multiple of the fundamental cycle.
* `Stacks.Chow.mem_tsupport_iff_genericPoint_coeff_ne_zero` — the support of such a cycle is the
  whole space or empty.
* `Stacks.Chow.isIntegral_of_connectedSpace_of_smooth` — a connected scheme smooth over a field
  is integral, so a connected fibre of a smooth morphism carries a unique generic point.
* `Stacks.Chow.relativeDimension_lt_of_ne_genericPoint` — on an irreducible scheme the relative
  dimension is strictly smaller away from the generic point.
* `Stacks.Chow.isClopen_supportOfFamily_of_specializes` — the support of a family of cycles is
  open and closed once membership in it is invariant along specializations.
* `Stacks.Chow.irreducibleComponent_eq_connectedComponent_of_smooth`,
  `Stacks.Chow.isClopen_irreducibleComponent_of_smooth` — on a scheme smooth over a field the
  irreducible component through a point is its connected component, and is open and closed.
* `Stacks.Chow.isLocallyConstant_of_specializes_eq` — a function whose value is unchanged along
  every specialization is locally constant.
* `Stacks.Chow.closure_singleton_eq_irreducibleComponent` — the closure of a generic point of an
  irreducible component is that component.
* `Stacks.Chow.isClopen_closure_of_subset_genericPoints_of_smooth` — on a scheme smooth over a
  field the closure of a set of generic points of irreducible components is open and closed.
* `Stacks.Chow.support_subset_genericPoints_of_relativeDimension_eq` — a cycle of relative
  dimension `k` is supported on generic points of components when every such generic point has
  relative dimension `k`.
* `Stacks.Chow.isClopen_tsupport_of_smooth` — the support of such a cycle on a scheme smooth
  over a field is open and closed.

## Implementation notes

The construction of the generic point of the irreducible component through a point, and its
specialization to that point, is inlined in the proof of
`Stacks.Chow.support_subset_genericPoints_of_relativeDimension_eq`; it duplicates the private
helper `exists_mem_genericPoints_specializes` of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GenericFibres`, which is not importable here.

## References

* [Stacks Project, Lemma 0H5B](https://stacks.math.columbia.edu/tag/0H5B)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Section 0H4E](https://stacks.math.columbia.edu/tag/0H4E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- A subset of a quasi-sober locally Noetherian space whose membership is unchanged along
every specialization is open: on a Noetherian open neighbourhood of a point the subset is
stable under specialization and under generalization, and there are only finitely many
irreducible components. -/
theorem isOpen_of_specializes_iff {X : Type u} [TopologicalSpace X] [QuasiSober X]
    (hX : IsLocallyNoetherianSpace X) {A : Set X}
    (hA : ∀ x y : X, x ⤳ y → (x ∈ A ↔ y ∈ A)) : IsOpen A := by
  rw [isOpen_iff_forall_mem_open]
  intro u hu
  obtain ⟨W, hWopen, huW, hWnoeth⟩ := hX u
  let _ : NoetherianSpace W := hWnoeth
  let _ : QuasiSober W := hWopen.isOpenEmbedding_subtypeVal.quasiSober
  have hspec : StableUnderSpecialization (Subtype.val ⁻¹' A : Set W) := fun a b hab ha ↦
    (hA a.1 b.1 ((subtype_specializes_iff a b).mp hab)).mp ha
  have hgen : StableUnderGeneralization (Subtype.val ⁻¹' A : Set W) := fun a b hab ha ↦
    (hA b.1 a.1 ((subtype_specializes_iff b a).mp hab)).mpr ha
  exact ⟨Subtype.val '' (Subtype.val ⁻¹' A : Set W), Set.image_preimage_subset _ _,
    hWopen.isOpenEmbedding_subtypeVal.isOpenMap _ (hspec.isOpen_of_stableUnderGeneralization hgen
      (NoetherianSpace.finite_irreducibleComponents (α := W))), ⟨⟨u, huW⟩, hu, rfl⟩⟩

/-- **Stacks Project, Lemma 0H5B**, topological step. A subset of a quasi-sober locally
Noetherian space whose membership is unchanged along every specialization is open and closed:
the complement satisfies the same hypothesis. -/
theorem isClopen_of_specializes_iff {X : Type u} [TopologicalSpace X] [QuasiSober X]
    (hX : IsLocallyNoetherianSpace X) {A : Set X}
    (hA : ∀ x y : X, x ⤳ y → (x ∈ A ↔ y ∈ A)) : IsClopen A := by
  refine ⟨?_, isOpen_of_specializes_iff hX hA⟩
  rw [← isOpen_compl_iff]
  exact isOpen_of_specializes_iff hX fun x y hxy ↦ not_congr (hA x y hxy)

/-! ### The weight of a point in a flat pullback with reduced inverse image -/

/-- **Stacks Project, Tag 02QU.** The weight with which a point `x` enters a flat pullback
along `h` is one as soon as `x` is a generic point of a component of the scheme-theoretic
inverse image of the reduced closure of `h x`, that inverse image is reduced, and the relative
dimension of `x` is the one being read.

The weight is by definition the multiplicity of that component, and a reduced closed subscheme
has multiplicity one at every generic point of a component. Together with the coefficient
formula for the base change of a family of cycles this is what makes the fibrewise coefficient
unchanged by a base change whose fibres stay reduced. -/
theorem flatPullbackWeight_eq_one_of_reduced (C : ChowSituation.{u}) {T Y : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (h : T ⟶ Y) (j : ℤ) (x : T)
    (hred : IsReduced (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subscheme))
    (ξ : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subscheme))
    (hξ : (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subschemeι) ξ.1 = x)
    (hdim : relativeDimension C.dimensionFunction sT x = j) :
    flatPullbackWeight C sT h j x = 1 := by
  classical
  let _ := hred
  unfold flatPullbackWeight closedSubschemeCycleCoeff
  have H : ∃ η : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({h.base x} : Set Y))).comap h).subscheme),
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({h.base x} : Set Y))).comap h).subschemeι) η.1 = x ∧
        relativeDimension C.dimensionFunction sT x = j :=
    ⟨ξ, hξ, hdim⟩
  rw [dite_eq_left H]
  exact componentMultiplicity_eq_one_of_reduced _ (Classical.choose H)

/-! ### Cycles on an integral scheme with a unique point of top relative dimension -/

/-- On an integral scheme whose generic point is the only point of relative dimension `k`, every
`k`-cycle is the integer multiple of the fundamental cycle `[Y]_k` by its own coefficient at the
generic point: at every other point both sides vanish, and `[Y]_k` has coefficient one at the
generic point because `Y` is integral. -/
theorem cycle_eq_smul_fundamentalCycle_of_unique_top_point (C : ChowSituation.{u})
    {Y : Scheme.{u}} [IsIntegral Y] (p : Y ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (hgen : relativeDimension C.dimensionFunction p (genericPoint Y) = k)
    (hlt : ∀ x : Y, x ≠ genericPoint Y → relativeDimension C.dimensionFunction p x < k)
    (c : CycleGroup C p k) :
    c = c.1 (genericPoint Y) • cycleAssociatedToClosedSubscheme C p (𝟙 Y) k := by
  have hmem : genericPoint Y ∈ genericPoints Y := genericPoint_mem_genericPoints Y
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x = genericPoint Y
  · subst x
    have hone : (cycleAssociatedToClosedSubscheme C p (𝟙 Y) k).1 (genericPoint Y) = 1 := by
      have h := cycleAssociatedToClosedSubscheme_apply C p (𝟙 Y) k ⟨genericPoint Y, hmem⟩ hgen
      rwa [componentMultiplicity_eq_one (𝟙 Y) hmem] at h
    change c.1 (genericPoint Y) = c.1 (genericPoint Y) *
      (cycleAssociatedToClosedSubscheme C p (𝟙 Y) k).1 (genericPoint Y)
    rw [hone, mul_one]
  · have hc : c.1 x = 0 := by
      by_contra hne
      exact (hlt x hx).ne ((mem_cyclesOfDimension_iff_forall_point C p k c.1).mp c.2 x hne)
    have hF : (cycleAssociatedToClosedSubscheme C p (𝟙 Y) k).1 x = 0 := by
      refine cycleAssociatedToClosedSubscheme_apply_eq_zero C p (𝟙 Y) k x ?_
      rintro ⟨ζ, hζ, -⟩
      have hmemζ : (ζ : Y) ∈ ({genericPoint Y} : Set Y) := by
        rw [← genericPoints_eq_singleton]
        exact ζ.2
      exact hx (hζ.symm.trans (Set.mem_singleton_iff.mp hmemζ))
    change c.1 x = c.1 (genericPoint Y) * (cycleAssociatedToClosedSubscheme C p (𝟙 Y) k).1 x
    rw [hc, hF, mul_zero]

/-- On an integral scheme whose generic point is the only point of relative dimension `k`, a
`k`-cycle has full support when its coefficient at the generic point is nonzero and empty
support otherwise: the support is closed and contains the generic point in the first case, and
the cycle is zero in the second. -/
theorem mem_tsupport_iff_genericPoint_coeff_ne_zero (C : ChowSituation.{u}) {Y : Scheme.{u}}
    [IsIntegral Y] (p : Y ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (hgen : relativeDimension C.dimensionFunction p (genericPoint Y) = k)
    (hlt : ∀ x : Y, x ≠ genericPoint Y → relativeDimension C.dimensionFunction p x < k)
    (c : CycleGroup C p k) (x : Y) :
    x ∈ tsupport (c.1 : AlgebraicCycle Y ℤ) ↔ c.1 (genericPoint Y) ≠ 0 := by
  refine ⟨fun hx hzero ↦ ?_, fun hne ↦ ?_⟩
  · have hc : c = 0 := by
      rw [cycle_eq_smul_fundamentalCycle_of_unique_top_point C p k hgen hlt c, hzero]
      simp
    rw [show (c.1 : AlgebraicCycle Y ℤ) = 0 from congrArg Subtype.val hc] at hx
    simp at hx
  · refine closure_mono (Set.singleton_subset_iff.mpr ?_)
      (specializes_iff_mem_closure.mp (genericPoint_specializes x))
    simpa only [Function.mem_support] using hne

/-! ### Connected smooth schemes over a field -/

/-- **Stacks Project, Tags 056S and 033N.** A connected scheme smooth over a field is integral.
Smoothness over a field makes the scheme regular, hence normal, and a locally Noetherian normal
scheme is a coproduct of integral schemes; connectedness forces the index set of that coproduct
to be a singleton. -/
@[ega "IV 19.7.5" "special case"]
theorem isIntegral_of_connectedSpace_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [Smooth p] [ConnectedSpace Y] : IsIntegral Y := by
  classical
  let _ : LocallyOfFiniteType p := inferInstance
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨ι, Z, -, hZint, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct_integral_normal Y).mp
      (isNormal_of_isRegular Y (isRegular_of_smooth_over_field p))
  let h : Y ≃ₜ (Σ i, Z i) := e.hom.homeomorph.trans (sigmaMk Z).symm
  have hclopen (i : ι) : IsClopen (h ⁻¹' Set.range (Sigma.mk i) : Set Y) :=
    isClopen_range_sigmaMk.preimage h.continuous
  have huniv (i : ι) (x : Z i) : (h ⁻¹' Set.range (Sigma.mk i) : Set Y) = Set.univ :=
    ((isClopen_iff.mp (hclopen i)).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨h.symm ⟨i, x⟩, by simp⟩))
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  have hfst (i : ι) (x : Z i) : (h y).1 = i := by
    obtain ⟨a, ha⟩ := Set.eq_univ_iff_forall.mp (huniv i x) y
    exact (congrArg Sigma.fst ha).symm
  let _ : Nonempty ι := ⟨(h y).1⟩
  let _ : Subsingleton ι := ⟨fun i j ↦ by
    let _ := hZint i
    let _ := hZint j
    obtain ⟨xi⟩ := (inferInstance : Nonempty (Z i))
    obtain ⟨xj⟩ := (inferInstance : Nonempty (Z j))
    rw [← hfst i xi, hfst j xj]⟩
  let _ : Unique ι := uniqueOfSubsingleton (Classical.arbitrary ι)
  let _ := hZint default
  exact IsIntegral.of_isIso (e ≪≫ Limits.coproductUniqueIso Z).inv

/-! ### Relative dimension drops away from the generic point -/

/-- The relative dimension strictly drops along a nontrivial specialization. -/
private theorem relativeDimension_lt_of_specializes (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] {x ξ : Y} (hspec : ξ ⤳ x) (hx : x ≠ ξ) :
    relativeDimension C.dimensionFunction p x < relativeDimension C.dimensionFunction p ξ := by
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction p
  rw [← hd x, ← hd ξ]
  exact d.strictAnti_specializes hspec fun hq ↦ hx hq.symm

/-- On an irreducible scheme locally of finite type over the base, the relative dimension is
strictly smaller at every point other than the generic point: by Stacks 02JW the relative
dimension is the underlying function of a dimension function, and a dimension function strictly
decreases along every nontrivial specialization. -/
theorem relativeDimension_lt_of_ne_genericPoint (C : ChowSituation.{u}) {Y : Scheme.{u}}
    [IrreducibleSpace Y] (p : Y ⟶ C.S) [LocallyOfFiniteType p] {x : Y}
    (hx : x ≠ genericPoint Y) :
    relativeDimension C.dimensionFunction p x <
      relativeDimension C.dimensionFunction p (genericPoint Y) :=
  relativeDimension_lt_of_specializes C p (genericPoint_specializes x) hx

/-! ### The support of a family of cycles -/

/-- **Stacks Project, Lemma 0H5B**, reduction step. The support of a family of `r`-cycles on the
fibres of a morphism locally of finite type over a locally Noetherian base is open and closed in
the total space as soon as membership in it is unchanged along every specialization of points of
the total space.

This is the step of the source which replaces local constancy of the coefficient function
`x ↦ n_x` by its invariance along specializations: the total space is locally Noetherian, being
locally of finite type over a locally Noetherian base, and on a locally Noetherian scheme a
subset invariant along specializations is open and closed. -/
@[stacks 0H5B "the support is clopen once membership is invariant along specializations"]
theorem isClopen_supportOfFamily_of_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {r : ℕ} (α : FamilyOfCycles f r)
    (hα : ∀ x y : X, x ⤳ y → (x ∈ supportOfFamily f α ↔ y ∈ supportOfFamily f α)) :
    IsClopen (supportOfFamily f α) :=
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isClopen_of_specializes_iff (isLocallyNoetherianSpace_of_isLocallyNoetherian X) hα

/-! ### Components of a smooth scheme over a field -/

/-- The connected component of a point of a scheme smooth over a field is open: the scheme is
locally of finite type over the field, hence locally Noetherian, hence locally connected. -/
@[sga "1 IX 5.1" "special case",
  sga "3 VIA 2.3" "special case",
  sga "3 X 5.11.0" "special case",
  sga "3 X 6.2" "special case"]
theorem isOpen_connectedComponent_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [Smooth p] (y : Y) : IsOpen (connectedComponent y) :=
  let _ : LocallyOfFiniteType p := inferInstance
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let _ : LocallyConnectedSpace Y := IsLocallyNoetherianSpace.locallyConnectedSpace _
    (isLocallyNoetherianSpace_of_isLocallyNoetherian Y)
  isOpen_connectedComponent

/-- The connected component of a point of a scheme smooth over a field, viewed as an open
subscheme, is integral: it is connected and smooth over the field. -/
theorem isIntegral_connectedComponent_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [Smooth p] (y : Y) (hopen : IsOpen (connectedComponent y)) :
    IsIntegral ((⟨connectedComponent y, hopen⟩ : Y.Opens) : Scheme.{u}) :=
  let U : Y.Opens := ⟨connectedComponent y, hopen⟩
  let _ : ConnectedSpace (U : Scheme.{u}) :=
    Subtype.connectedSpace (s := connectedComponent y) isConnected_connectedComponent
  isIntegral_of_connectedSpace_of_smooth (U.ι ≫ p)

/-- On a scheme smooth over a field the irreducible component through a point is its connected
component. One inclusion holds because an irreducible set is connected; the other because the
connected component, being an open subscheme smooth over the field and connected, is integral
and therefore irreducible, so it cannot properly contain an irreducible component. -/
@[sga "3 X 5.14.0" "special case"]
theorem irreducibleComponent_eq_connectedComponent_of_smooth {k : Type u} [Field k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [Smooth p] (y : Y) :
    irreducibleComponent y = connectedComponent y := by
  have hopen : IsOpen (connectedComponent y) := isOpen_connectedComponent_of_smooth p y
  let _ : IsIntegral ((⟨connectedComponent y, hopen⟩ : Y.Opens) : Scheme.{u}) :=
    isIntegral_connectedComponent_of_smooth p y hopen
  have hirr : IsIrreducible (connectedComponent y) := isIrreducible_iff_irreducibleSpace.mpr
    (inferInstance : IrreducibleSpace ((⟨connectedComponent y, hopen⟩ : Y.Opens) : Scheme.{u}))
  have hsub : irreducibleComponent y ⊆ connectedComponent y :=
    isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  exact subset_antisymm hsub ((irreducibleComponent_mem_irreducibleComponents y).2 hirr hsub)

/-- **Stacks Project, Lemma 0H5B**, geometric step. On a scheme smooth over a field every
irreducible component is open and closed, so it is an open subscheme and is itself smooth over
the field. This is what makes the unique component of a smooth fibre through a point reduced
after any extension of the base field. -/
@[stacks 0H5B "components of a smooth scheme over a field are open and closed",
  sga "7 VIII 5.2" "special case"]
theorem isClopen_irreducibleComponent_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [Smooth p] (y : Y) : IsClopen (irreducibleComponent y) := by
  rw [irreducibleComponent_eq_connectedComponent_of_smooth p y]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_smooth p y⟩

/-! ### Local constancy of a function invariant along specializations -/

/-- **Stacks Project, Lemma 0H5B**, topological reduction for a function. A function on a
quasi-sober locally Noetherian space whose value is unchanged along every specialization is
locally constant: membership in each of its fibres is unchanged along specializations, hence
each fibre is open.

This is the sentence of the source which replaces local constancy of the coefficient function
`x ↦ n_x` by the implication `x' ⤳ x → n_{x'} = n_x`. -/
@[stacks 0H5B "the reduction of local constancy of the fibrewise coefficient function to its
invariance along specializations; not that invariance itself"]
theorem isLocallyConstant_of_specializes_eq {A : Type u} [TopologicalSpace A] [QuasiSober A]
    {β : Type*} (hA : IsLocallyNoetherianSpace A) {n : A → β}
    (hn : ∀ x y : A, x ⤳ y → n x = n y) : IsLocallyConstant n :=
  IsLocallyConstant.iff_isOpen_fiber.2 fun b ↦
    isOpen_of_specializes_iff hA fun x y hxy ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hn x y hxy]

/-! ### Generic points of irreducible components -/

/-- The closure of a generic point of an irreducible component is the component through that
point: the component is closed and contains the point, so it contains the closure, and the
closure is a maximal irreducible set. -/
theorem closure_singleton_eq_irreducibleComponent {A : Type u} [TopologicalSpace A] {ξ : A}
    (hξ : ξ ∈ genericPoints A) : closure ({ξ} : Set A) = irreducibleComponent ξ :=
  have hmem : closure ({ξ} : Set A) ∈ irreducibleComponents A := hξ
  have hsub : closure ({ξ} : Set A) ⊆ irreducibleComponent ξ :=
    isClosed_irreducibleComponent.closure_subset_iff.2
      (Set.singleton_subset_iff.2 mem_irreducibleComponent)
  subset_antisymm hsub (hmem.2 isIrreducible_irreducibleComponent hsub)

/-- **Stacks Project, Lemma 0H5B**, geometric step. On a scheme smooth over a field the closure
of any set of generic points of irreducible components is open and closed.

That closure is the union of the components of those points; on a smooth scheme each such
component is a connected component, and two connected components either coincide or are
disjoint, so the union is closed as well as open. -/
@[sga "3 X 5.14.0" "special case"]
theorem isClopen_closure_of_subset_genericPoints_of_smooth {k : Type u} [Field k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [Smooth p] {A : Set Y}
    (hA : A ⊆ genericPoints ↥Y) : IsClopen (closure A) := by
  have hUopen : IsOpen (⋃ ξ ∈ A, connectedComponent ξ) :=
    isOpen_biUnion fun ξ _ ↦ isOpen_connectedComponent_of_smooth p ξ
  have hUclosed : IsClosed (⋃ ξ ∈ A, connectedComponent ξ) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    refine ⟨connectedComponent y, fun z hz hzmem ↦ ?_,
      isOpen_connectedComponent_of_smooth p y, mem_connectedComponent⟩
    obtain ⟨ξ, hξA, hzξ⟩ := Set.mem_iUnion₂.mp hzmem
    refine hy (Set.mem_iUnion₂.mpr ⟨ξ, hξA, ?_⟩)
    rw [connectedComponent_eq hzξ, ← connectedComponent_eq hz]
    exact mem_connectedComponent
  have hclosure : closure A = ⋃ ξ ∈ A, connectedComponent ξ := by
    refine subset_antisymm (closure_minimal (fun ξ hξ ↦
      Set.mem_iUnion₂.mpr ⟨ξ, hξ, mem_connectedComponent⟩) hUclosed)
      (Set.iUnion₂_subset fun ξ hξ ↦ ?_)
    rw [← irreducibleComponent_eq_connectedComponent_of_smooth p ξ,
      ← closure_singleton_eq_irreducibleComponent (hA hξ)]
    exact closure_mono (Set.singleton_subset_iff.mpr hξ)
  exact ⟨isClosed_closure, by rwa [hclosure]⟩

/-! ### The support of a cycle of top relative dimension -/

/-- A cycle of relative dimension `k` is supported on generic points of irreducible components
as soon as every such generic point has relative dimension `k`.

Indeed the relative dimension is the underlying function of a dimension function, which drops
strictly along every nontrivial specialization, and the generic point of the component through
a point specializes to that point. -/
theorem support_subset_genericPoints_of_relativeDimension_eq (C : ChowSituation.{u})
    {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (hgen : ∀ ξ ∈ genericPoints ↥Y, relativeDimension C.dimensionFunction p ξ = k)
    (c : CycleGroup C p k) :
    Function.support (c.1 : AlgebraicCycle Y ℤ) ⊆ genericPoints ↥Y := by
  intro x hx
  have hdimx : relativeDimension C.dimensionFunction p x = k :=
    (mem_cyclesOfDimension_iff_forall_point C p k c.1).mp c.2 x (Function.mem_support.mp hx)
  obtain ⟨ξ, hξmem, hspec⟩ : ∃ ξ ∈ genericPoints ↥Y, ξ ⤳ x := by
    refine ⟨(genericPoints.ofComponent
        ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩).1,
      (genericPoints.ofComponent _).2, ?_⟩
    rw [specializes_iff_mem_closure, genericPoints.isGenericPoint_ofComponent]
    exact mem_irreducibleComponent
  by_cases hxξ : x = ξ
  · exact hxξ ▸ hξmem
  · exact absurd hdimx
      ((relativeDimension_lt_of_specializes C p hspec hxξ).trans_eq (hgen ξ hξmem)).ne

/-- **Stacks Project, Lemma 0H5B** over the spectrum of a field. The support of a cycle of
relative dimension `k` on a scheme smooth over a field is open and closed, provided every
generic point of an irreducible component has relative dimension `k`; that proviso is what
being smooth of relative dimension `k` supplies.

Such a cycle is supported on generic points of irreducible components, and on a scheme smooth
over a field the closure of a set of such points is a union of connected components. -/
@[stacks 0H5B "the support of a cycle of top relative dimension on a scheme smooth over a field
is open and closed; neither the statement over a general base nor local constancy of the
fibrewise coefficient function"]
theorem isClopen_tsupport_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [Smooth p] (j : ℤ)
    (hgen : ∀ ξ ∈ genericPoints ↥Y,
      relativeDimension (fieldChowSituation k).dimensionFunction p ξ = j)
    (c : CycleGroup (fieldChowSituation k) p j) :
    IsClopen (tsupport (c.1 : AlgebraicCycle Y ℤ)) :=
  isClopen_closure_of_subset_genericPoints_of_smooth p
    (support_subset_genericPoints_of_relativeDimension_eq (fieldChowSituation k) p j hgen c)

end Stacks.Chow

end

