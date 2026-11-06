module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyClosedValuative
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.UniversallyClosedAffineSpaceTest
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.FiniteSeparable
public import StacksFrontier.RingTheory.KrullAkizuki

/-!
# Universal closedness over a locally Noetherian algebraic space

Let `f : X ⟶ Y` be a morphism of finite type of algebraic spaces over a scheme `S`, with `Y`
locally Noetherian. Stacks 0H1Y compares five conditions on `f`:

1. `f` is universally closed;
2. `f` satisfies the existence part of the valuative criterion;
3. for one surjective étale morphism `V ⟶ Y` from a scheme, the base change of `f` to every
   affine space `𝐀ⁿ_V` is closed;
4. every valuative square whose valuation ring is a discrete valuation ring acquires a dotted
   arrow after a finite separable extension of the fraction field and passage to a dominating
   discrete valuation ring;
5. every valuative square whose valuation ring is a discrete valuation ring acquires a dotted
   arrow after an extension of the fraction field and passage to a dominating valuation ring.

## Main results

* `IsDiscreteValuationRing.of_isLocalHom_of_finite`: a valuation ring dominating a discrete
  valuation ring in a finite extension of its fraction field is a discrete valuation ring, by
  Krull–Akizuki (Stacks 00PG).
* `AlgebraicGeometry.Space.isClosedMorphism_of_discreteExistence`: under the standing
  hypotheses, condition (5) makes `f` closed.
* `AlgebraicGeometry.Space.universallyClosed_of_discreteExistence`: (5) implies (1).
* `AlgebraicGeometry.Space.discreteFiniteSeparableExistence_of_valuativeCriterion_existence`:
  (2) implies (4).
* `AlgebraicGeometry.Space.universallyClosed_tfae_of_isLocallyNoetherian`: **Stacks 0H1Y**, the
  five conditions are equivalent for `f` decent, for instance quasi-separated.

## Implementation notes

The source states Stacks 0H1Y with no condition on `f` beyond finite type, and in that
generality the statement is false:
`AlgebraicGeometry.Space.not_forall_universallyClosed_tfae_of_isLocallyNoetherian` is its
negation. The witness is the structure morphism `𝔸¹_ℚ/ℤ ⟶ Spec ℚ`, which is of finite type over
a Noetherian scheme and universally closed (Stacks 03IV), but does not satisfy the existence part
of the valuative criterion, by
`AlgebraicGeometry.AffineLineTranslation.not_valuativeCriterion_existence_structureMap`
(the failure recorded in the introduction of Stacks section 03K9), and is not decent. The wrong
step of the source's proof is its first sentence, which cites Stacks 0CM9 (Lemma 70.20.2) and
Stacks 03KA (Lemma 67.42.1) for the equivalence of (1), (2) and (3): Stacks 03KA only gives
(2) ⇒ (1), for `f` quasi-compact. The converse (1) ⇒ (2) is Stacks 0A3X (Lemma 67.42.2) for `f`
quasi-separated, and Stacks 03M6 (Lemma 68.17.11) for `f` quasi-compact and decent. So the
equivalence is stated for `f` decent, which holds for instance when `f` is quasi-separated
(Stacks 03M5); `f` is quasi-compact, being of finite type.

Every other implication holds without decency and is stated on its own: (1) ⇔ (3) is Stacks
0CM9, (2) ⇒ (4) ⇒ (5) ⇒ (1) is `discreteFiniteSeparableExistence_of_valuativeCriterion_existence`
followed by `universallyClosed_of_discreteExistence`, and (2) ⇒ (1) is Stacks 03KA.

The implication (5) ⇒ (1) follows the source. Condition (5) passes to base changes, so by
Stacks 0CM9 it is enough that `f` is closed when `Y` is locally Noetherian. A closed set `T` of
points of `X` is the point set of its reduced closed subspace `Z` (Stacks 03IQ), the composite
`Z ⟶ X ⟶ Y` is again of finite type, and a point of `Y` in the closure of the image of `T` is
reached by the closed point of a discrete valuation ring whose generic point comes from `Z`
(Stacks 0CMC). Condition (5) provides a dotted arrow after a dominating extension, and the
closed point of the extended valuation ring maps to a point of `X` which specializes a point
of `T`, hence lies in `T`, and lies over the given point.

## References

* [Stacks Project, Tag 0H1Y](https://stacks.math.columbia.edu/tag/0H1Y)
* [Stacks Project, Tag 03IV](https://stacks.math.columbia.edu/tag/03IV)
* [Stacks Project, Tag 03K9](https://stacks.math.columbia.edu/tag/03K9)
* [Stacks Project, Tag 03M6](https://stacks.math.columbia.edu/tag/03M6)
* [Stacks Project, Tag 0A3X](https://stacks.math.columbia.edu/tag/0A3X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Krull–Akizuki for a dominating valuation ring -/

/-- A valuation ring dominating a discrete valuation ring `A`, inside a finite extension of the
fraction field of `A`, is a discrete valuation ring.

It is Noetherian by Krull–Akizuki (Stacks 00PG), it is not a field because a uniformizer of `A`
maps to a nonzero nonunit, and a Noetherian valuation ring which is not a field is a discrete
valuation ring. -/
theorem IsDiscreteValuationRing.of_isLocalHom_of_finite
    {A K A' K' : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing A'] [IsDomain A'] [ValuationRing A'] [Field K'] [Algebra A' K']
    [IsFractionRing A' K'] [Algebra K K'] [Module.Finite K K']
    (φ : A →+* A') [IsLocalHom φ]
    (hφ : (algebraMap A' K').comp φ = (algebraMap K K').comp (algebraMap A K)) :
    IsDiscreteValuationRing A' := by
  let : Algebra A K' := ((algebraMap K K').comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hle : (algebraMap A K').range ≤ (algebraMap A' K').range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨φ a, RingHom.congr_fun hφ a⟩
  have hN : IsNoetherianRing (algebraMap A' K').range :=
    krull_akizuki A K K' (IsDiscreteValuationRing.ringKrullDim_eq_one A) _ hle
  have hinj' : Function.Injective (algebraMap A' K').rangeRestrict := fun x y h ↦
    IsFractionRing.injective A' K' (congrArg Subtype.val h)
  have : IsNoetherianRing A' := isNoetherianRing_of_ringEquiv _
    (RingEquiv.ofBijective _ ⟨hinj', (algebraMap A' K').rangeRestrict_surjective⟩).symm
  have hinj : Function.Injective φ := .of_comp (f := algebraMap A' K') (by
    rw [← RingHom.coe_comp, hφ, RingHom.coe_comp]
    exact (algebraMap K K').injective.comp (IsFractionRing.injective A K))
  have hnf : ¬ IsField A' := by
    intro hF
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    have h0 : φ ϖ ≠ 0 := (map_ne_zero_iff φ hinj).mpr hϖ.ne_zero
    let := hF.toField
    exact hϖ.not_isUnit (isUnit_of_map_unit φ ϖ (isUnit_iff_ne_zero.mpr h0))
  have h := (IsDiscreteValuationRing.TFAE A' hnf).out 1 2
  exact h.mpr (inferInstanceAs (ValuationRing A'))

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_NoetherianUniversallyClosed
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Base change of the discrete existence condition -/

/-- The base change of a morphism every valuative square of which over a discrete valuation
ring acquires a dotted arrow after a dominating extension has the same property.

A valuative square for the base change `b` induces one for `p` with the same valuation ring, as
in Stacks 03IY; a dominating extension and a dotted arrow there define one for the square of
`b` through the universal property of the cartesian square. -/
theorem discreteExistence_of_isPullback
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : F ⟶ F'} {b : F ⟶ G} {p : F' ⟶ G'} {q : G ⟶ G'} (sq : IsPullback a b p q)
    (hp : ∀ v : ValuativeSquare p, IsDiscreteValuationRing v.R →
      ∃ e : v.DominatingExtension, Nonempty e.square.Lift) :
    ∀ v : ValuativeSquare b, IsDiscreteValuationRing v.R →
      ∃ e : v.DominatingExtension, Nonempty e.square.Lift := by
  intro v hv
  let vp : ValuativeSquare p :=
    { R := v.R, K := v.K, ring_mem := v.ring_mem, field_mem := v.field_mem, base := v.base
      generic := v.generic ≫ a, special := v.special ≫ q
      comm := by
        rw [Category.assoc, sq.w, ← Category.assoc, v.comm', Category.assoc] }
  obtain ⟨e, ⟨l⟩⟩ := hp vp hv
  have hcompat : l.map ≫ p = (yoneda.map e.specialOver ≫ v.special) ≫ q := by
    rw [l.special_comm, e.special_comm, Category.assoc]
  let vb : ValuativeSquare b :=
    { R := e.square.R, K := e.square.K
      ring_mem := e.square.ring_mem, field_mem := e.square.field_mem
      base := e.square.base
      generic := yoneda.map e.genericOver ≫ v.generic
      special := yoneda.map e.specialOver ≫ v.special
      comm := by
        rw [Category.assoc, v.comm', ← Category.assoc,
          e.yonedaMap_genericOver_comp_fracHom, Category.assoc] }
  let ev : v.DominatingExtension :=
    { square := vb
      ringMap := e.ringMap, fieldMap := e.fieldMap, isLocalHom := e.isLocalHom
      fraction_comm := e.fraction_comm, base_comm := e.base_comm
      genericOver := e.genericOver, genericOver_left := e.genericOver_left
      specialOver := e.specialOver, specialOver_left := e.specialOver_left
      generic_comm := rfl, special_comm := rfl }
  have hgenA : (yoneda.map e.square.fracHom ≫
        sq.lift l.map (yoneda.map e.specialOver ≫ v.special) hcompat) ≫ a =
      (yoneda.map e.genericOver ≫ v.generic) ≫ a := by
    rw [Category.assoc, sq.lift_fst, Category.assoc]
    exact l.generic_comm'.trans e.generic_comm
  have hgenB : (yoneda.map e.square.fracHom ≫
        sq.lift l.map (yoneda.map e.specialOver ≫ v.special) hcompat) ≫ b =
      (yoneda.map e.genericOver ≫ v.generic) ≫ b := by
    rw [Category.assoc, sq.lift_snd, Category.assoc, v.comm']
    exact e.generic_comp v.special
  exact ⟨ev, ⟨{ map := sq.lift l.map (yoneda.map e.specialOver ≫ v.special) hcompat
                generic_comm := sq.hom_ext hgenA hgenB
                special_comm := sq.lift_snd _ _ _ }⟩⟩

/-! ### Closedness from the discrete existence condition -/

section PointTopology

attribute [local instance] pointTopology

variable (B S hS)

/-- **A discrete valuation ring reaching a point of the closure of an image lifts.** Let
`i : Z ⟶ X` and `f : X ⟶ Y` be morphisms of presheaves, let `T` be a closed set of points of `X`
containing the image of `Z`, and let `d` be a discrete valuation ring reaching a point `y` of `Y`
through `i ≫ f`, as in Stacks 0CMC. If every valuative square for `f` over a discrete valuation
ring acquires a dotted arrow after a dominating extension, then `y` is the image of a point of
`T`.

The diagram `d` is a valuative square for `f`; the closed point of the extended valuation ring
maps to a point of `X` specializing the generic point, which lies in `T`. -/
theorem exists_mem_pointsMap_eq_of_discreteValuationSpecialization
    {Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) (i : Z ⟶ X) (f : X ⟶ Y) (y : points B S hS Y)
    (d : DiscreteValuationSpecialization B S hS (i ≫ f) hZ hY y)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hiT : Set.range (pointsMap B S hS Z i) ⊆ T)
    (hval : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∃ e : q.DominatingExtension, Nonempty e.square.Lift) :
    ∃ x ∈ T, pointsMap B S hS X f x = y := by
  classical
  let A := d.valuationRing
  let K := d.generic.carrier
  let p : FieldValuedPoint B S hS X := FieldValuedPoint.map B S hS Z i d.generic
  -- The structure morphism of the generic point factors through the valuation ring.
  have hbase : d.generic.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ d.toBase := by
    have hw := congrArg (fun t ↦ B.inclusion.map t) (Over.w d.genericToValuation)
    simp only [Functor.map_comp] at hw
    have hleft : B.inclusion.map d.genericToValuation.left =
        Spec.map (CommRingCat.ofHom (algebraMap A K)) := d.genericToValuation_spec
    rw [hleft] at hw
    exact hw.symm
  let k : siteObject B S hS d.generic.contained
      (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ d.toBase) ⟶
        d.generic.siteObject B S hS Z :=
    Over.homMk (𝟙 (B.obj d.generic.contained)) (by
      apply ObjectProperty.hom_ext
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom]
      exact hbase)
  let fracHom : siteObject B S hS d.generic.contained
      (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ d.toBase) ⟶
        siteObject B S hS d.valuation_contained d.toBase :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) :
      B.obj d.generic.contained ⟶ B.obj d.valuation_contained)
  have hk : k ≫ d.genericToValuation = fracHom := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show B.inclusion.map (𝟙 (B.obj d.generic.contained)) ≫
        B.inclusion.map d.genericToValuation.left = _
    rw [B.inclusion.map_id, Category.id_comp]
    exact d.genericToValuation_spec
  let v : ValuativeSquare f :=
    { R := A, K := K, ring_mem := d.valuation_contained, field_mem := d.generic.contained
      base := d.toBase
      generic := yoneda.map k ≫ yonedaEquiv.symm d.generic.value ≫ i
      special := d.toTarget
      comm := by
        show (yoneda.map k ≫ yonedaEquiv.symm d.generic.value ≫ i) ≫ f =
          yoneda.map fracHom ≫ d.toTarget
        simp only [← hk, Functor.map_comp, Category.assoc, d.commutes] }
  have hgeneric : v.generic = yoneda.map k ≫ yonedaEquiv.symm p.value :=
    congrArg (yoneda.map k ≫ ·) (yonedaEquiv_symm_naturality_right _ i d.generic.value)
  obtain ⟨e, ⟨l⟩⟩ := hval v d.isDVR
  obtain ⟨r, hpr, hfr⟩ := exists_specializes_pointsMap_eq_of_lift v e l p k hgeneric
  have hpT : p.class B S hS X ∈ T := hiT ⟨d.generic.class B S hS Z, rfl⟩
  exact ⟨r, hpr.mem_closed hT hpT, hfr.trans d.maps_closedPoint⟩

/-- **Closedness from the discrete existence condition.** A morphism of finite type of algebraic
spaces over `S`, with locally Noetherian target, every valuative square of which over a discrete
valuation ring acquires a dotted arrow after a dominating extension, is closed.

A closed set of points is the point set of its reduced closed subspace (Stacks 03IQ), whose
composite with the morphism is again of finite type, and a point in the closure of the image is
reached by a discrete valuation ring through that composite by Stacks 0CMC. -/
theorem isClosedMorphism_of_discreteExistence {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFiniteType B S hS f)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hval : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∃ e : q.DominatingExtension, Nonempty e.square.Lift) :
    IsClosedMorphism B S hS f := by
  intro T hT
  let Z := reducedClosedSubspace B S hS X hX T hT
  have hZ : IsClosedSubspace B S hS Z := isClosedSubspace_reducedClosedSubspace B S hS X hX T hT
  have hZT : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = T :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT
  have hg : IsFiniteType B S hS (Z.ι ≫ f) :=
    isFiniteType_comp B S hS hZ.1 hX hY Z.ι f
      (isFiniteType_of_isClosedImmersion B S hS Z.ι hZ.2) hf
  have hrange : Set.range (pointsMap B S hS Z.toFunctor (Z.ι ≫ f)) =
      pointsMap B S hS X f '' T := by
    rw [pointsMap_comp, Set.range_comp, hZT]
  rw [← closure_subset_iff_isClosed]
  intro y hy
  rw [← hrange] at hy
  obtain ⟨d⟩ := nonempty_discreteValuationSpecialization B S hS (Z.ι ≫ f) hZ.1 hY hg hNoeth y hy
  obtain ⟨x, hxT, hxy⟩ := exists_mem_pointsMap_eq_of_discreteValuationSpecialization B S hS
    hZ.1 hY Z.ι f y d T hT hZT.subset hval
  exact ⟨x, hxT, hxy⟩

end PointTopology

variable (B S hS)

/-- **Stacks 0H1Y, (5) implies (1).** A morphism of finite type of algebraic spaces over `S`,
with locally Noetherian target, every valuative square of which over a discrete valuation ring
acquires a dotted arrow after an extension of the fraction field and passage to a dominating
valuation ring, is universally closed. No separation hypothesis is needed.

By Stacks 0CM9 it is enough that the base change of `f` to affine `n`-space over a locally
Noetherian surjective étale chart of `Y` be closed for every `n`; that base change is of finite
type over a locally Noetherian scheme and inherits the hypothesis, so
`isClosedMorphism_of_discreteExistence` applies. -/
theorem universallyClosed_of_discreteExistence {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFiniteType B S hS f)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hval : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∃ e : q.DominatingExtension, Nonempty e.square.Lift) :
    UniversallyClosed B S hS f := by
  obtain ⟨V, g, hgsurj, hgetale, hVnoeth⟩ := hNoeth
  have hV := isAlgebraicSpace_yoneda B S hS V
  have h0CM9 := (universallyClosed_tfae_of_isQuasiCompact B S hS hX hY f hf.2).out 3 1
  refine h0CM9.mp ⟨V, g, (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V g).mp hgsurj,
      (isEtale_iff_presheaf_of_yoneda B S hS g).mpr hgetale, fun n ↦ ?_⟩
  obtain ⟨W, a, e, he⟩ := exists_isAffineSpaceOver B S hS V n
  refine ⟨W, a, ⟨e, he⟩, ?_⟩
  have hW := isAlgebraicSpace_yoneda B S hS W
  let g' := yoneda.map a ≫ g
  have sq : IsPullback (pullback.snd g' f) (pullback.fst g' f) f g' :=
    (IsPullback.of_hasPullback g' f).flip
  have hWnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) := by
    let : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hVnoeth
    have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map a) := by
      rw [he]
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map a)
  exact isClosedMorphism_of_discreteExistence B S hS
    (isAlgebraicSpace_pullback B S hS g' f hW hX hY) hW (pullback.fst g' f)
    (IsFiniteType.of_isPullback B S hS sq.flip hX hY hf)
    (hasEtaleLocalProperty_of_representable B S hS _ _ W (Iso.refl _) hWnoeth)
    (discreteExistence_of_isPullback sq hval)

/-- **Stacks 0H1Y, (2) implies (4).** If a morphism of algebraic spaces over `S` satisfies the
existence part of the valuative criterion, every valuative square over a discrete valuation
ring acquires a dotted arrow after a finite separable extension of the fraction field and
passage to a dominating discrete valuation ring.

The extension can be taken finite separable by Stacks 03KH, and the dominating valuation ring
is then a discrete valuation ring by Krull–Akizuki. -/
theorem discreteFiniteSeparableExistence_of_valuativeCriterion_existence
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hex : ValuativeCriterion.Existence f) :
    ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∃ e : q.DominatingExtension,
        IsDiscreteValuationRing e.square.R ∧
          (letI := e.fieldMap.toAlgebra
           Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
          Nonempty e.square.Lift := by
  intro q hq
  obtain ⟨e, ⟨hfin, hsep⟩, hlift⟩ :=
    (valuativeCriterion_existence_iff_finiteSeparable B S hS hX hY f).mp hex q
  let : Algebra q.K e.square.K := e.fieldMap.toAlgebra
  have := e.isLocalHom
  exact ⟨e, IsDiscreteValuationRing.of_isLocalHom_of_finite e.ringMap e.fraction_comm,
    ⟨hfin, hsep⟩, hlift⟩

/-- **Stacks 0H1Y.** Let `f : X ⟶ Y` be a decent morphism of finite type of algebraic spaces
over `S`, with `Y` locally Noetherian; for instance `f` quasi-separated. The following are
equivalent:

1. `f` is universally closed;
2. `f` satisfies the existence part of the valuative criterion;
3. there are an object `V` of the site and a surjective étale morphism `V ⟶ Y` such that for
   every `n` the base change of `f` to affine `n`-space over `V` is closed;
4. every valuative square for `f` whose valuation ring is a discrete valuation ring acquires a
   dotted arrow after a finite separable extension of the fraction field and passage to a
   dominating discrete valuation ring;
5. every valuative square for `f` whose valuation ring is a discrete valuation ring acquires a
   dotted arrow after an extension of the fraction field and passage to a dominating valuation
   ring.

The source omits decency, and without it the statement is false. This is
`AlgebraicGeometry.Space.not_forall_universallyClosed_tfae_of_isLocallyNoetherian`
(in `StacksFrontier.AlgebraicGeometry.Spaces.NoetherianUniversallyClosedCounterexample`), whose
statement is this theorem with the hypothesis `IsDecent B S hS f` removed:
```
¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
    IsAlgebraicSpace B S hS Y → ∀ f : X ⟶ Y, IsFiniteType B S hS f →
    HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
    List.TFAE
      [UniversallyClosed B S hS f,
        ValuativeCriterion.Existence f,
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
              IsAffineSpaceOver B S hS V W n a ∧
                IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f),
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension,
            IsDiscreteValuationRing e.square.R ∧
              (letI := e.fieldMap.toAlgebra
               Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
              Nonempty e.square.Lift,
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension, Nonempty e.square.Lift]
```
The witness is the structure morphism `𝔸¹_ℚ/ℤ ⟶ Spec ℚ` of the quotient of the affine line by
the integer translations: it is of finite type over the Noetherian scheme `Spec ℚ` and
universally closed (Stacks 03IV), but the `ℚ((t))`-point `1/t` extends to no valuation ring
dominating `ℚ[[t]]`, so (1) holds and (2) fails. With decency, (1) implies (2) by Stacks 03M6,
`f` being quasi-compact as it is of finite type. -/
@[stacks 0H1Y "for f decent (e.g. quasi-separated); without decency the statement is false, \
  see not_forall_universallyClosed_tfae_of_isLocallyNoetherian"]
theorem universallyClosed_tfae_of_isLocallyNoetherian {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X_alg : IsAlgebraicSpace B S hS X) (Y_alg : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (decent : IsDecent B S hS f) (ft : IsFiniteType B S hS f)
    (noeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    List.TFAE
      [UniversallyClosed B S hS f,
        ValuativeCriterion.Existence f,
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsSurjective B S hS g ∧ IsEtale B S hS g ∧
            ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
              IsAffineSpaceOver B S hS V W n a ∧
                IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f),
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension,
            IsDiscreteValuationRing e.square.R ∧
              (letI := e.fieldMap.toAlgebra
               Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
              Nonempty e.square.Lift,
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          ∃ e : q.DominatingExtension, Nonempty e.square.Lift] := by
  have h0CM9 := universallyClosed_tfae_of_isQuasiCompact B S hS X_alg Y_alg f ft.2
  tfae_have 1 → 2 :=
    (universallyClosed_iff_valuativeCriterion_existence_of_isDecent B S hS X_alg Y_alg f ft.2
      decent).mp
  tfae_have 1 ↔ 3 := h0CM9.out 1 3
  tfae_have 2 → 4 :=
    discreteFiniteSeparableExistence_of_valuativeCriterion_existence B S hS X_alg Y_alg f
  tfae_have 4 → 5 := fun h q hq ↦ (h q hq).imp fun _ he ↦ he.2.2
  tfae_have 5 → 1 := universallyClosed_of_discreteExistence B S hS X_alg Y_alg f ft noeth
  tfae_finish

end AlgebraicGeometry.Space

end
