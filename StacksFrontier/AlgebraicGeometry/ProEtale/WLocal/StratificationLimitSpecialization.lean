module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.PointClosure
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationStrataPoints
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings
public import StacksCore.Tactic.StacksAttribute

/-!
# Specializations into the limiting closed subscheme of a stratification

Let `A` be a commutative ring, let `X_w = Spec A_w` be the inverse limit of the finite vanishing
stratifications of `Spec A`, and let `Z ⊆ X_w` be the inverse limit of the finite closed strata.
Every point of `X_w` specializes to a point of `Z`, and to only one.

## Main results

* `AlgebraicGeometry.ProEtale.exists_specializes_to_closedScheme`: a point of `X_w` specializes
  to some point of `Z`.
* `AlgebraicGeometry.ProEtale.eq_of_specializes_to_closedScheme`: a point of `X_w` specializes to
  at most one point of `Z`.

## Implementation notes

Both results are proved for an arbitrary bundle of limiting data `L : StratificationLimit A`, not
only for the canonical construction, so they apply to any realization of the two inverse systems.

Existence is a nonemptiness statement about a compatible family of closed subsets of the finite
closed strata, and follows from the general fact that such a family has a nonempty inverse limit
along a cofiltered system of schemes with affine transition morphisms; the point so produced is
identified with the image of a point of `Z` by the limit property on underlying sets.

Uniqueness is first reduced to the corresponding statement in `Spec A`, where two distinct points
are separated by an element `f` of `A`; the stage `E = {f}` then splits as two clopen pieces,
which a common generalization cannot meet at once. Once the images in `Spec A` agree, the two
points agree at every finite stage, hence in the limit.

## References

* [Stacks Project, Tag 0975](https://stacks.math.columbia.edu/tag/0975)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-! ### Existence of a specialization in the limiting closed subscheme -/

/-- Every point of a finite stage `X_E` specializes to a point of its closed stratum `Z_E`. -/
private theorem exists_specializes_closedStrataMap (E : Finset A)
    (x : Spec (.of (stratificationRing E))) :
    ∃ z : closedStrata E, x ⤳ (closedStrataMap E).base z := by
  obtain ⟨q, hqx, hq⟩ :=
    isClosed_closure.exists_closed_singleton ⟨x, subset_closure (Set.mem_singleton x)⟩
  obtain ⟨z, rfl⟩ := closedPoints_mem_closedStrataMap_range E q hq
  exact ⟨z, specializes_iff_mem_closure.mpr hqx⟩

/-- Two points of the limit of a diagram of schemes with a limit-preserving forgetful functor
agree when all their projections agree. -/
private theorem eq_of_forall_base_eq {J : Type*} [Category J] {F : J ⥤ Scheme.{u}}
    [PreservesLimit F Scheme.forget] (c : Cone F) (hc : IsLimit c) {a b : c.pt}
    (h : ∀ i, (c.π.app i).base a = (c.π.app i).base b) : a = b := by
  have hlim : IsLimit (Scheme.forget.mapCone c) := isLimitOfPreserves Scheme.forget hc
  let T := ULift.{u, 0} Unit
  let fa : T ⟶ Scheme.forget.obj c.pt := TypeCat.ofHom fun _ => a
  let fb : T ⟶ Scheme.forget.obj c.pt := TypeCat.ofHom fun _ => b
  have hab : fa = fb := hlim.hom_ext fun i => by
    ext
    exact h i
  simpa [fa, fb] using congrArg
    (fun g : T ⟶ Scheme.forget.obj c.pt => TypeCat.Hom.hom g (ULift.up ())) hab

/-- Every point of `X_w` specializes to a point of the limiting closed subscheme `Z`. -/
theorem exists_specializes_to_closedScheme (L : StratificationLimit A)
    (y : stratificationLimitScheme (A := A)) :
    ∃ z : L.closedScheme, y ⤳ L.inclusion.base z := by
  classical
  let I := (Finset A)ᵒᵖ
  let D : I ⥤ Scheme := L.closedDiagram
  let c : Cone D := Cone.mk L.closedScheme L.closedProjection
  have hc : IsLimit c := L.closedIsLimit
  let ambientPoint (i : I) : Spec (.of (stratificationRing (Opposite.unop i))) :=
    (L.schemeProjection.app i ≫ (L.schemeStage (Opposite.unop i)).hom).base y
  let closedPointMap (i : I) :
      D.obj i ⟶ Spec (.of (stratificationRing (Opposite.unop i))) := by
    simpa only [Opposite.op_unop] using
      ((L.closedStage (Opposite.unop i)).hom ≫ closedStrataMap (Opposite.unop i))
  let Z (i : I) : Set (D.obj i) :=
    (closedPointMap i).base ⁻¹' closure ({ambientPoint i} : Set _)
  have hclosed (i : I) : IsClosed (Z i) :=
    isClosed_closure.preimage (closedPointMap i).continuous
  have hnonempty (i : I) : (Z i).Nonempty := by
    obtain ⟨z, hz⟩ := exists_specializes_closedStrataMap (Opposite.unop i) (ambientPoint i)
    refine ⟨(L.closedStage (Opposite.unop i)).inv.base z, ?_⟩
    have hstagePoint : (L.closedStage (Opposite.unop i)).hom.base
        ((L.closedStage (Opposite.unop i)).inv.base z) = z := by
      simp
    have hmap : (closedPointMap i).base ((L.closedStage (Opposite.unop i)).inv.base z) =
        (closedStrataMap (Opposite.unop i)).base z := by
      change (closedStrataMap (Opposite.unop i)).base
        ((L.closedStage (Opposite.unop i)).hom.base
          ((L.closedStage (Opposite.unop i)).inv.base z)) = _
      rw [hstagePoint]
    change (closedPointMap i).base _ ∈ closure ({ambientPoint i} : Set _)
    rw [hmap]
    exact specializes_iff_mem_closure.mp hz
  have hcompact (i : I) : IsCompact (Z i) := by
    have : IsAffine (closedStrata (Opposite.unop i)) := closedStrata_isAffine _
    have : IsAffine (D.obj i) := IsAffine.of_isIso (L.closedStage (Opposite.unop i)).hom
    exact (hclosed i).isCompact
  have hmapsTo : ∀ {i j : I} (f : i ⟶ j), Set.MapsTo (D.map f).base (Z i) (Z j) := by
    intro i j f z hz
    let E₂ := Opposite.unop i
    let E₁ := Opposite.unop j
    have hE : E₁ ⊆ E₂ := leOfHom f.unop
    have hf : f = (homOfLE hE).op := Subsingleton.elim _ _
    let t := closedStrataTransition E₁ E₂ hE
    let p := stratificationSchemeMap E₁ E₂ hE
    have hclosedTransition := L.closedTransition E₁ E₂ hE
    rw [← hf] at hclosedTransition
    have hschemeTransition := L.schemeTransition E₁ E₂ hE
    rw [← hf] at hschemeTransition
    have hβ : D.map f ≫ (L.closedStage E₁).hom ≫ closedStrataMap E₁ =
        (L.closedStage E₂).hom ≫ closedStrataMap E₂ ≫ p := by
      rw [reassoc_of% hclosedTransition, t.property]
    have hproj : L.schemeProjection.app j =
        L.schemeProjection.app i ≫ L.schemeDiagram.map f := by
      simpa using (L.schemeProjection.naturality f)
    have hα : L.schemeProjection.app j ≫ (L.schemeStage E₁).hom =
        L.schemeProjection.app i ≫ (L.schemeStage E₂).hom ≫ p := by
      rw [hproj, Category.assoc, hschemeTransition]
    have hpoint : (closedPointMap j).base ((D.map f).base z) =
        p.base ((closedPointMap i).base z) := by
      simpa [closedPointMap, Scheme.Hom.comp_base, Function.comp_apply] using
        congrArg (fun g => g z) hβ
    have hambient : ambientPoint j = p.base (ambientPoint i) := by
      simpa [ambientPoint, Scheme.Hom.comp_base, Function.comp_apply] using
        congrArg (fun g => g y) hα
    have hspec : ambientPoint i ⤳ (closedPointMap i).base z := specializes_iff_mem_closure.mpr hz
    change (closedPointMap j).base ((D.map f).base z) ∈ closure ({ambientPoint j} : Set _)
    rw [hambient, hpoint]
    exact specializes_iff_mem_closure.mp (hspec.map p.continuous)
  let : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f) := by
    intro i j f
    have : IsAffine (closedStrata (Opposite.unop i)) := closedStrata_isAffine _
    have : IsAffine (closedStrata (Opposite.unop j)) := closedStrata_isAffine _
    have : IsAffine (D.obj i) := IsAffine.of_isIso (L.closedStage (Opposite.unop i)).hom
    have : IsAffine (D.obj j) := IsAffine.of_isIso (L.closedStage (Opposite.unop j)).hom
    infer_instance
  let : ∀ i : I, CompactSpace (D.obj i) := by
    intro i
    have : IsAffine (closedStrata (Opposite.unop i)) := closedStrata_isAffine _
    have : IsAffine (D.obj i) := IsAffine.of_isIso (L.closedStage (Opposite.unop i)).hom
    infer_instance
  obtain ⟨z, hz⟩ := exists_mem_of_isClosed_of_nonempty D c hc Z hclosed hnonempty hcompact hmapsTo
  let x (i : I) : L.schemeDiagram.obj i := (L.schemeProjection.app i).base (L.inclusion.base z)
  have hcompat : ∀ ⦃i j : I⦄ (f : i ⟶ j), (L.schemeDiagram.map f).base (x i) = x j := by
    intro i j f
    have hproj : L.schemeProjection.app j =
        L.schemeProjection.app i ≫ L.schemeDiagram.map f := by
      simpa using (L.schemeProjection.naturality f)
    simpa [x] using (congrArg (fun g => g (L.inclusion.base z)) hproj).symm
  have hclosure : ∀ i : I, x i ∈ closure ({(L.schemeProjection.app i).base y} : Set _) := by
    intro i
    let E := Opposite.unop i
    have hs : ambientPoint i ⤳ (closedPointMap i).base ((L.closedProjection.app i).base z) :=
      specializes_iff_mem_closure.mpr (hz i)
    have hinc := congrArg (fun g => g z) (L.inclusion_spec E)
    have hleft : (L.schemeStage E).inv.base (ambientPoint i) =
        (L.schemeProjection.app i).base y := by
      change ((L.schemeStage E).hom ≫ (L.schemeStage E).inv).base
        ((L.schemeProjection.app i).base y) = _
      rw [Iso.hom_inv_id]
      rfl
    have hright : (L.schemeStage E).inv.base
        ((closedPointMap i).base ((L.closedProjection.app i).base z)) = x i := by
      have hinc' : (L.schemeStage E).hom.base (x i) =
          (closedPointMap i).base ((L.closedProjection.app i).base z) := by
        simpa [x, closedPointMap, Scheme.Hom.comp_base, Function.comp_apply,
          Category.assoc] using hinc
      rw [← hinc']
      change ((L.schemeStage E).hom ≫ (L.schemeStage E).inv).base (x i) = _
      rw [Iso.hom_inv_id]
      rfl
    have hs' := hs.map (L.schemeStage E).inv.continuous
    rw [hleft, hright] at hs'
    exact specializes_iff_mem_closure.mp hs'
  let : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (L.schemeDiagram.map f) := by
    intro i j f
    have : IsAffine (L.schemeDiagram.obj i) :=
      IsAffine.of_isIso (L.schemeStage (Opposite.unop i)).hom
    have : IsAffine (L.schemeDiagram.obj j) :=
      IsAffine.of_isIso (L.schemeStage (Opposite.unop j)).hom
    infer_instance
  let : PreservesLimit L.schemeDiagram Scheme.forget :=
    preservesLimit_forget_of_isCofiltered_of_isAffineHom L.schemeDiagram
  let cScheme : Cone L.schemeDiagram :=
    Cone.mk (stratificationLimitScheme (A := A)) L.schemeProjection
  obtain ⟨q, hq, _⟩ :=
    existsUnique_mem_closure_singleton_of_compatible L.schemeDiagram cScheme L.schemeIsLimit y x
      hcompat hclosure
  have hcoord : ∀ i : I,
      (L.schemeProjection.app i).base q = (L.schemeProjection.app i).base (L.inclusion.base z) :=
    fun i => by simpa [x] using hq.2 i
  have hq_eq : q = L.inclusion.base z :=
    eq_of_forall_base_eq cScheme L.schemeIsLimit hcoord
  exact ⟨z, hq_eq ▸ specializes_iff_mem_closure.mpr hq.1⟩

/-! ### Uniqueness of the specialization in the limiting closed subscheme -/

/-- For the stratification by a single element `f`, a point of a stratum records whether `f`
vanishes at it. -/
private theorem singletonStratum_mem_iff (f : A)
    (i : {E' : Finset A // E' ⊆ ({f} : Finset A)}) (p : PrimeSpectrum A)
    (hp : p ∈ locallyClosedPoints (stratumIdeal {f} i) (stratumOpenElement i.val)) :
    f ∈ i.val ↔ f ∉ p.asIdeal := by
  classical
  refine ⟨fun hfi => ?_, fun hfn => ?_⟩
  · have hi : i.val = {f} :=
      Finset.Subset.antisymm i.property (Finset.singleton_subset_iff.mpr hfi)
    simpa [show stratumOpenElement i.val = f by simp [stratumOpenElement, hi]] using hp.2
  · by_contra hfi
    exact hfn (hp.1 (Ideal.subset_span
      (Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self f, hfi⟩)))

/-- A point of `Z` is given at each finite stage by a vanishing pattern and a prime of the
corresponding coordinate ring, compatibly with its images in `Spec A` and in `X_E`. -/
private theorem closedPoint_stageData (L : StratificationLimit A) (z : L.closedScheme)
    (E : Finset A) :
    ∃ (i : {E' : Finset A // E' ⊆ E}) (q : PrimeSpectrum (stratumCoordinateRing E i)),
      (L.inclusion ≫ Spec.map (CommRingCat.ofHom
          (stratificationColimitAlgebraMap (A := A)))).base z =
        specPointEquiv A (PrimeSpectrum.comap
          (locallyClosedCoordinateMap (stratumIdeal E i) (stratumOpenElement i.val)) q) ∧
      (L.schemeProjection.app (Opposite.op E) ≫ (L.schemeStage E).hom).base
          (L.inclusion.base z) ∈
        Set.range (PrimeSpectrum.comap (Pi.evalRingHom
          (fun j : {E' : Finset A // E' ⊆ E} =>
            localizationRing (stratumIdeal E j) (stratumOpenElement j.val)) i)) ∧
      closedStrataPoint E i q =
        (L.closedStage E).hom.base ((L.closedProjection.app (Opposite.op E)).base z) := by
  let w : closedStrata E :=
    (L.closedStage E).hom.base ((L.closedProjection.app (Opposite.op E)).base z)
  obtain ⟨i, q, hw⟩ := exists_closedStrataPoint_eq E w
  refine ⟨i, q, ?_, ?_, hw⟩
  · have h := congrArg (fun g => g z) (inclusion_stage_factor L E)
    have h' : (L.inclusion ≫ Spec.map (CommRingCat.ofHom
        (stratificationColimitAlgebraMap (A := A)))).base z =
        (closedStrataMap E ≫
          Spec.map (CommRingCat.ofHom (stratificationAlgebraMap E))).base w := by
      simpa [w, Scheme.Hom.comp_base, Function.comp_apply] using h
    rw [← hw] at h'
    exact h'.trans (closedStrataMap_point_formula E i q)
  · have h := congrArg (fun g => g z) (L.inclusion_spec E)
    change (L.schemeProjection.app (Opposite.op E) ≫ (L.schemeStage E).hom).base
      (L.inclusion.base z) = (closedStrataMap E).base w at h
    rw [h, ← hw]
    exact closedStrataMap_mem_component E i q

/-- A point of `X_w` specializes to at most one point of the limiting closed subscheme `Z`. -/
theorem eq_of_specializes_to_closedScheme (L : StratificationLimit A)
    {y z z' : stratificationLimitScheme (A := A)}
    (hz : z ∈ Set.range L.inclusion.base) (hz' : z' ∈ Set.range L.inclusion.base)
    (hyz : y ⤳ z) (hyz' : y ⤳ z') : z = z' := by
  classical
  obtain ⟨zc, hzc⟩ := hz
  obtain ⟨zc', hzc'⟩ := hz'
  have hyz₀ : y ⤳ L.inclusion.base zc := by simpa [hzc] using hyz
  have hyz'₀ : y ⤳ L.inclusion.base zc' := by simpa [hzc'] using hyz'
  let baseMap := L.inclusion ≫
    Spec.map (CommRingCat.ofHom (stratificationColimitAlgebraMap (A := A)))
  let x := baseMap.base zc
  let x' := baseMap.base zc'
  have hbase : x = x' := by
    by_contra hx
    let p := (specPointEquiv A).symm x
    let p' := (specPointEquiv A).symm x'
    have hIdealNe : p.asIdeal ≠ p'.asIdeal := fun heq => hx <| by
      calc x = specPointEquiv A p := ((specPointEquiv A).apply_symm_apply x).symm
        _ = specPointEquiv A p' := congrArg (specPointEquiv A) (PrimeSpectrum.ext heq)
        _ = x' := (specPointEquiv A).apply_symm_apply x'
    have hsep : ∃ f : A,
        (f ∈ p.asIdeal ∧ f ∉ p'.asIdeal) ∨ (f ∉ p.asIdeal ∧ f ∈ p'.asIdeal) := by
      by_contra hsep
      exact hIdealNe (SetLike.ext fun a => by_contra fun h => hsep ⟨a, by tauto⟩)
    obtain ⟨f, hf⟩ := hsep
    let E : Finset A := {f}
    obtain ⟨i, q, hxq, hcomp, -⟩ := closedPoint_stageData L zc E
    obtain ⟨j, r, hx'r, hcomp', -⟩ := closedPoint_stageData L zc' E
    have hpEq : p = PrimeSpectrum.comap
        (locallyClosedCoordinateMap (stratumIdeal E i) (stratumOpenElement i.val)) q :=
      (specPointEquiv A).injective (((specPointEquiv A).apply_symm_apply x).trans hxq)
    have hp'Eq : p' = PrimeSpectrum.comap
        (locallyClosedCoordinateMap (stratumIdeal E j) (stratumOpenElement j.val)) r :=
      (specPointEquiv A).injective (((specPointEquiv A).apply_symm_apply x').trans hx'r)
    have hpLoc : p ∈ locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val) := by
      rw [hpEq, ← locallyClosedCoordinateMap_range]
      exact ⟨q, rfl⟩
    have hp'Loc : p' ∈ locallyClosedPoints (stratumIdeal E j) (stratumOpenElement j.val) := by
      rw [hp'Eq, ← locallyClosedCoordinateMap_range]
      exact ⟨r, rfl⟩
    have hfi := singletonStratum_mem_iff f i p hpLoc
    have hfj := singletonStratum_mem_iff f j p' hp'Loc
    have hij : i ≠ j := by
      rintro rfl
      rcases hf with ⟨hfp, hfn⟩ | ⟨hfn, hfp⟩
      · exact hfi.mp (hfj.mpr hfn) hfp
      · exact hfj.mp (hfi.mpr hfn) hfp
    let family := fun k : {E' : Finset A // E' ⊆ E} =>
      localizationRing (stratumIdeal E k) (stratumOpenElement k.val)
    let stageMap := L.schemeProjection.app (Opposite.op E) ≫ (L.schemeStage E).hom
    have hycomp : stageMap.base y ∈
        Set.range (PrimeSpectrum.comap (Pi.evalRingHom family i)) :=
      (hyz₀.map stageMap.continuous).mem_open
        (ProetaleWContractible.isClopen_range_comap_evalRingHom family i).isOpen hcomp
    have hycomp' : stageMap.base y ∈
        Set.range (PrimeSpectrum.comap (Pi.evalRingHom family j)) :=
      (hyz'₀.map stageMap.continuous).mem_open
        (ProetaleWContractible.isClopen_range_comap_evalRingHom family j).isOpen hcomp'
    exact Set.disjoint_left.mp
      (ProetaleWContractible.disjoint_range_comap_evalRingHom family i j hij) hycomp hycomp'
  have hstage (E : Finset A) :
      (L.closedProjection.app (Opposite.op E)).base zc =
        (L.closedProjection.app (Opposite.op E)).base zc' := by
    obtain ⟨i, q, hxq, -, hrep⟩ := closedPoint_stageData L zc E
    obtain ⟨j, r, hx'r, -, hrep'⟩ := closedPoint_stageData L zc' E
    have hqbase : PrimeSpectrum.comap
        (locallyClosedCoordinateMap (stratumIdeal E i) (stratumOpenElement i.val)) q =
        PrimeSpectrum.comap
          (locallyClosedCoordinateMap (stratumIdeal E j) (stratumOpenElement j.val)) r :=
      (specPointEquiv A).injective (hxq.symm.trans (hbase.trans hx'r))
    have hqLoc : PrimeSpectrum.comap
        (locallyClosedCoordinateMap (stratumIdeal E i) (stratumOpenElement i.val)) q ∈
        locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val) := by
      rw [← locallyClosedCoordinateMap_range]
      exact ⟨q, rfl⟩
    have hrLoc : PrimeSpectrum.comap
        (locallyClosedCoordinateMap (stratumIdeal E i) (stratumOpenElement i.val)) q ∈
        locallyClosedPoints (stratumIdeal E j) (stratumOpenElement j.val) := by
      rw [hqbase, ← locallyClosedCoordinateMap_range]
      exact ⟨r, rfl⟩
    obtain rfl := stratumIndex_eq_of_mem E i j _ hqLoc hrLoc
    obtain rfl := locallyClosedCoordinateMap_comap_injective (stratumIdeal E i)
      (stratumOpenElement i.val) hqbase
    exact schemeIso_base_injective (L.closedStage E) (hrep.symm.trans hrep')
  let D := L.closedDiagram
  let : ∀ {i j : (Finset A)ᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    closedDiagram_hasAffineTransitions L
  let : PreservesLimit D Scheme.forget :=
    preservesLimit_forget_of_isCofiltered_of_isAffineHom D
  have hzcEq : zc = zc' :=
    eq_of_forall_base_eq (Cone.mk L.closedScheme L.closedProjection) L.closedIsLimit
      fun i => hstage i.unop
  rw [← hzc, ← hzc', hzcEq]

end AlgebraicGeometry.ProEtale

end
