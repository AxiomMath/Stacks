module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# The localization sequence for cycles

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `i : Y ⟶ X` be a closed immersion and let `j : U ⟶ X` be an open immersion whose
image is the complement of the image of `i`. Stacks 02RC says that

  `Z_k(Y) ⟶ Z_k(X) ⟶ Z_k(U) ⟶ 0`

is exact: restriction of cycles to `U` is surjective, and a cycle on `X` restricts to zero on
`U` exactly when it is a proper pushforward from `Y`.

Restriction is `Stacks.Chow.cycleGroupRestrict`, which reads off the coefficients of a cycle at
the points of `U`; it is flat pullback along `j` in relative dimension zero. Neither statement
needs `Y` to carry the reduced induced structure.

## Main definitions

* `Stacks.Chow.cycleComap` — the coefficientwise inverse image of a cycle along a morphism with
  injective underlying map.
* `Stacks.Chow.cycleGroupRestrict` — restriction of `k`-cycles along an open immersion.

## Main results

* `Stacks.Chow.relativeDimension_comp_of_bijective_residueFieldMap` — relative dimension is
  unchanged by a morphism inducing an isomorphism on residue fields, hence by an immersion.
* `Stacks.Chow.cycleGroupRestrict_eq_flatPullback` — restriction along an open immersion is flat
  pullback in relative dimension zero.
* `Stacks.Chow.cycleGroupRestrict_surjective` — **Stacks 02RC**: restriction to the open
  complement is surjective.
* `Stacks.Chow.cycleGroupRestrict_eq_zero_iff` — **Stacks 02RC**: a cycle restricts to zero on
  the open complement exactly when it is a proper pushforward from the closed complement.

## References

* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Relative dimension along an immersion -/

/-- The relative dimension of Stacks 02JW is unchanged by a morphism that induces an isomorphism
on residue fields. -/
theorem relativeDimension_comp_of_bijective_residueFieldMap {X Z S : Scheme.{u}}
    (δ : DimensionFunction S) (i : Z ⟶ X) (p : X ⟶ S) (z : Z)
    (hz : Function.Bijective (i.residueFieldMap z).hom) :
    relativeDimension δ (i ≫ p) z = relativeDimension δ p (i.base z) := by
  let _ : Algebra (S.residueField (p.base (i.base z))) (X.residueField (i.base z)) :=
    (p.residueFieldMap (i.base z)).hom.toAlgebra
  let _ : Algebra (S.residueField (p.base (i.base z))) (Z.residueField z) :=
    ((i ≫ p).residueFieldMap z).hom.toAlgebra
  have hcm : ∀ r, (i.residueFieldMap z).hom
      (algebraMap (S.residueField (p.base (i.base z))) (X.residueField (i.base z)) r) =
      algebraMap (S.residueField (p.base (i.base z))) (Z.residueField z) r := by
    intro r
    show (i.residueFieldMap z).hom ((p.residueFieldMap (i.base z)).hom r) =
      ((i ≫ p).residueFieldMap z).hom r
    rw [Scheme.residueFieldMap_comp]
    rfl
  let e : X.residueField (i.base z) ≃ₐ[S.residueField (p.base (i.base z))] Z.residueField z :=
    { __ := RingEquiv.ofBijective (i.residueFieldMap z).hom hz
      commutes' := hcm }
  show δ (p.base (i.base z)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (p.base (i.base z)))
        (Z.residueField z)) : ℤ) =
    δ (p.base (i.base z)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (p.base (i.base z)))
        (X.residueField (i.base z))) : ℤ)
  rw [e.trdeg_eq]

/-- The relative dimension of Stacks 02JW is unchanged by an open immersion. -/
theorem relativeDimension_comp_isOpenImmersion {X U S : Scheme.{u}} (δ : DimensionFunction S)
    (j : U ⟶ X) [IsOpenImmersion j] (p : X ⟶ S) (z : U) :
    relativeDimension δ (j ≫ p) z = relativeDimension δ p (j.base z) :=
  relativeDimension_comp_of_bijective_residueFieldMap δ j p z
    (ConcreteCategory.bijective_of_isIso _)

/-- Over the base, the relative dimension at a point of `U` is that of its image under an open
immersion `j : U ⟶ X`. -/
private theorem relativeDimension_eq_of_isOpenImmersion_of_comp_eq {X U S : Scheme.{u}}
    (δ : DimensionFunction S) (sX : X ⟶ S) (sU : U ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) (z : U) : relativeDimension δ sU z = relativeDimension δ sX (j.base z) := by
  subst hj
  exact relativeDimension_comp_isOpenImmersion δ j sX z

/-! ### The inverse image of a cycle along an injective morphism -/

/-- The coefficientwise inverse image of a cycle along a morphism with injective underlying map:
the coefficient at `y` is the coefficient of the original cycle at the image of `y`. -/
def cycleComap {Y X : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Injective f.base)
    (c : AlgebraicCycle X ℤ) : AlgebraicCycle Y ℤ where
  toFun y := c (f.base y)
  supportWithinDomain' _ _ := trivial
  supportLocallyFiniteWithinDomain' y _ := by
    obtain ⟨t, ht, htfin⟩ := c.supportLocallyFiniteWithinDomain' (f.base y) trivial
    refine ⟨f.base ⁻¹' t, f.continuous.continuousAt ht, ?_⟩
    refine Set.Finite.of_finite_image (f := f.base) (htfin.subset ?_) hf.injOn
    rintro w ⟨v, ⟨hvt, hvne⟩, rfl⟩
    exact ⟨hvt, hvne⟩

/-- The coefficient of `Stacks.Chow.cycleComap f hf c` at `y` is the coefficient of `c` at
`f y`. -/
@[simp]
theorem cycleComap_apply {Y X : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Injective f.base)
    (c : AlgebraicCycle X ℤ) (y : Y) : cycleComap f hf c y = c (f.base y) :=
  rfl

/-- The inverse image of the zero cycle is zero. -/
@[simp]
theorem cycleComap_zero {Y X : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Injective f.base) :
    cycleComap f hf 0 = 0 :=
  Function.locallyFinsuppWithin.ext fun _ ↦ rfl

/-- The inverse image of cycles is additive. -/
@[simp]
theorem cycleComap_add {Y X : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Injective f.base)
    (c d : AlgebraicCycle X ℤ) :
    cycleComap f hf (c + d) = cycleComap f hf c + cycleComap f hf d :=
  Function.locallyFinsuppWithin.ext fun _ ↦ rfl

/-- The inverse image of a `k`-cycle along an open immersion is a `k`-cycle. -/
theorem cycleComap_mem_cyclesOfDimension_of_isOpenImmersion (C : ChowSituation.{u})
    {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ)
    {c : AlgebraicCycle X ℤ} (hc : c ∈ cyclesOfDimension C sX k) :
    cycleComap j j.isOpenEmbedding.injective c ∈ cyclesOfDimension C sU k := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro z hz
  rw [relativeDimension_eq_of_isOpenImmersion_of_comp_eq _ sX sU j hj]
  exact (mem_cyclesOfDimension_iff_forall_point C sX k c).mp hc _ hz

/-- The inverse image of a `k`-cycle along a closed immersion is a `k`-cycle. -/
theorem cycleComap_mem_cyclesOfDimension_of_isClosedImmersion (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sY) (k : ℤ)
    {c : AlgebraicCycle X ℤ} (hc : c ∈ cyclesOfDimension C sX k) :
    cycleComap i i.isClosedEmbedding.injective c ∈ cyclesOfDimension C sY k := by
  subst hi
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro y hy
  rw [relativeDimension_comp_closedImmersion]
  exact (mem_cyclesOfDimension_iff_forall_point C sX k c).mp hc _ hy

/-! ### Restriction of cycles along an open immersion -/

/-- Restriction of `k`-cycles along an open immersion `j : U ⟶ X` over the base: the coefficient
at a point of `U` is the coefficient at its image in `X`. -/
def cycleGroupRestrict (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) :
    CycleGroup C sX k →+ CycleGroup C sU k where
  toFun c := ⟨cycleComap j j.isOpenEmbedding.injective c.1,
    cycleComap_mem_cyclesOfDimension_of_isOpenImmersion C sX sU j hj k c.2⟩
  map_zero' := Subtype.ext (cycleComap_zero j j.isOpenEmbedding.injective)
  map_add' c d := Subtype.ext (cycleComap_add j j.isOpenEmbedding.injective c.1 d.1)

/-- The coefficient of the restriction of a `k`-cycle `c` at a point `z` of `U` is the
coefficient of `c` at `j z`. -/
@[simp]
theorem cycleGroupRestrict_apply (C : ChowSituation.{u}) {X U : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
    [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) (c : CycleGroup C sX k) (z : U) :
    (cycleGroupRestrict C sX sU j hj k c).1 z = c.1 (j.base z) :=
  rfl

/-- Restriction along the inclusion of an open subscheme is
`Stacks.Chow.cycleGroupOpensRestrict`. -/
theorem cycleGroupOpensRestrict_eq_cycleGroupRestrict (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (V : X.Opens) (k : ℤ) :
    cycleGroupOpensRestrict C sX V k = cycleGroupRestrict C sX (V.ι ≫ sX) V.ι rfl k :=
  rfl

/-! ### Restriction is flat pullback in relative dimension zero -/

/-- **Stacks 02NJ.** An open immersion has relative dimension zero. -/
theorem relativeDimension_of_isOpenImmersion {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : AlgebraicGeometry.RelativeDimension j 0 :=
  (locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance

/-- **Stacks 02QU.** A point of `U` occurs with multiplicity one in the scheme-theoretic inverse
image along an open immersion `j : U ⟶ X` of the reduced closure of its image. -/
theorem flatPullbackWeight_of_isOpenImmersion (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (m : ℤ) (z : U)
    (hz : relativeDimension C.dimensionFunction sU z = m) :
    flatPullbackWeight C sU j m z = 1 := by
  have hcomap := comap_integralComponentAt_of_isOpenImmersion j z
  have hint : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  have hmem : genericPoint (integralComponentAt z).subscheme ∈
      genericPoints (integralComponentAt z).subscheme :=
    genericPoint_mem_genericPoints _
  have hgen : (integralComponentAt z).subschemeι.base
      (genericPoint (integralComponentAt z).subscheme) = z :=
    genericPointOf_integralComponentAt z
  have hdim : relativeDimension C.dimensionFunction sU
      ((integralComponentAt z).subschemeι.base
        (genericPoint (integralComponentAt z).subscheme)) = m := by
    rwa [hgen]
  have hkey : (cycleAssociatedToClosedSubscheme C sU
      (integralComponentAt z).subschemeι m).1 z = 1 := by
    have h := cycleAssociatedToClosedSubscheme_apply C sU
      (integralComponentAt z).subschemeι m ⟨_, hmem⟩ hdim
    rw [componentMultiplicity_eq_one (integralComponentAt z).subschemeι hmem] at h
    simpa only [hgen] using h
  have he := congrArg (fun K : U.IdealSheafData ↦
    (cycleAssociatedToClosedSubscheme C sU K.subschemeι m).1 z) hcomap
  show (cycleAssociatedToClosedSubscheme C sU
    ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j.base z} : Set X))).comap j).subschemeι m).1 z = 1
  exact he.trans hkey

/-- **Stacks 02RB.** Restriction of cycles along an open immersion is flat pullback along it in
relative dimension zero. -/
theorem cycleGroupRestrict_eq_flatPullback (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    (hr : AlgebraicGeometry.RelativeDimension j 0) (k : ℤ) (c : CycleGroup C sX k) :
    (cycleGroupRestrict C sX sU j hj k c).1 =
      (flatPullback C sU sX j hj 0 hr k c).1 := by
  refine Function.locallyFinsuppWithin.ext fun z ↦ ?_
  rw [cycleGroupRestrict_apply, flatPullback_apply]
  by_cases hc : c.1 (j.base z) = 0
  · rw [hc, zero_mul]
  · have hdim : relativeDimension C.dimensionFunction sX (j.base z) = k :=
      (mem_cyclesOfDimension_iff_forall_point C sX k c.1).mp c.2 _ hc
    have hdimU : relativeDimension C.dimensionFunction sU z = k + ((0 : ℕ) : ℤ) := by
      rw [relativeDimension_eq_of_isOpenImmersion_of_comp_eq _ sX sU j hj]
      simpa using hdim
    rw [flatPullbackWeight_of_isOpenImmersion C sU j (k + ((0 : ℕ) : ℤ)) z hdimU, mul_one]

/-! ### Surjectivity of restriction -/

/-- The extension by zero of a `k`-cycle on an open subscheme is a `k`-cycle on the ambient
scheme. -/
theorem map_mem_cyclesOfDimension_of_isOpenImmersion (C : ChowSituation.{u})
    {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hj : j ≫ sX = sU) (k : ℤ) (d : CycleGroup C sU k) :
    AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
        (relativeDimension C.dimensionFunction sX) d.1 ∈ cyclesOfDimension C sX k := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro x hx
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply] at hx
  obtain ⟨z, hzx, hterm⟩ := exists_ne_zero_of_finsum_mem_ne_zero hx
  simp only [AlgebraicCycle.mapCoeff] at hterm
  have hdz : relativeDimension C.dimensionFunction sU z = k :=
    (mem_cyclesOfDimension_iff_forall_point C sU k d.1).mp d.2 z (mul_ne_zero_iff.mp hterm).1
  rw [← hzx, ← relativeDimension_eq_of_isOpenImmersion_of_comp_eq _ sX sU j hj, hdz]

/-- Restriction of cycles along an open immersion is surjective. -/
@[stacks 02RC "surjectivity onto the open complement"]
theorem cycleGroupRestrict_surjective (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) :
    Function.Surjective (cycleGroupRestrict C sX sU j hj k) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  intro d
  refine ⟨⟨AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
    (relativeDimension C.dimensionFunction sX) d.1,
    map_mem_cyclesOfDimension_of_isOpenImmersion C sX sU j hj k d⟩, ?_⟩
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  have hfibre : j.base ⁻¹' {j.base z} = {z} := by
    rw [← Set.image_singleton, j.isOpenEmbedding.injective.preimage_image]
  rw [cycleGroupRestrict_apply]
  show AlgebraicCycle.map j (relativeDimension C.dimensionFunction sU)
    (relativeDimension C.dimensionFunction sX) d.1 (j.base z) = d.1 z
  rw [AlgebraicCycle.map, Function.locallyFinsupp.map_apply, hfibre, finsum_mem_singleton,
    AlgebraicCycle.mapCoeff,
    ← relativeDimension_eq_of_isOpenImmersion_of_comp_eq _ sX sU j hj,
    residueDegree_eq_one_of_isOpenImmersion]
  simp

/-! ### The kernel of restriction -/

/-- A cycle vanishing off the image of a closed immersion is the proper pushforward of its own
inverse image along that closed immersion. -/
theorem properPushforward_cycleComap (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sY) (k : ℤ) (c : CycleGroup C sX k)
    (hc : ∀ x : X, x ∉ Set.range i.base → c.1 x = 0) :
    properPushforward C sY sX i hi k
        ⟨cycleComap i i.isClosedEmbedding.injective c.1,
          cycleComap_mem_cyclesOfDimension_of_isClosedImmersion C sX sY i hi k c.2⟩ = c := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  rw [properPushforward_apply]
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨y, rfl⟩ := hx
    have hfibre : i.base ⁻¹' {i.base y} = {y} := by
      rw [← Set.image_singleton, i.isClosedEmbedding.injective.preimage_image]
    have hdim : relativeDimension C.dimensionFunction sY y =
        relativeDimension C.dimensionFunction sX (i.base y) := by
      subst hi
      exact relativeDimension_comp_closedImmersion C.dimensionFunction i sX y
    rw [hfibre, finsum_mem_singleton, cycleComap_apply, hdim,
      residueDegree_eq_one_of_isClosedImmersion]
    simp
  · rw [Set.preimage_singleton_eq_empty.mpr hx, finsum_mem_empty]
    exact (hc x hx).symm

/-- A cycle restricts to zero on the open complement exactly when it is the proper pushforward of
a cycle on the closed complement. -/
@[stacks 02RC "kernel of restriction"]
theorem cycleGroupRestrict_eq_zero_iff (C : ChowSituation.{u}) {X Y U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ sX = sY) (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    (hcomplement : Set.range i.base = (Set.range j.base)ᶜ) (k : ℤ) (c : CycleGroup C sX k) :
    cycleGroupRestrict C sX sU j hj k c = 0 ↔
      ∃ d : CycleGroup C sY k, properPushforward C sY sX i hi k d = c := by
  constructor
  · intro hz
    have hoff : ∀ x : X, x ∉ Set.range i.base → c.1 x = 0 := by
      intro x hx
      obtain ⟨z, rfl⟩ : x ∈ Set.range j.base := by simpa [hcomplement] using hx
      simpa [cycleGroupRestrict_apply] using congrArg (fun e : CycleGroup C sU k ↦ e.1 z) hz
    exact ⟨_, properPushforward_cycleComap C sX sY i hi k c hoff⟩
  · rintro ⟨d, rfl⟩
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    have hfibre : i.base ⁻¹' {j.base z} = ∅ := by
      rw [Set.preimage_singleton_eq_empty, hcomplement]
      exact fun h ↦ h ⟨z, rfl⟩
    rw [cycleGroupRestrict_apply, properPushforward_apply, hfibre, finsum_mem_empty]
    rfl

end Stacks.Chow

end
