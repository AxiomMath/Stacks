module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback

/-!
# Exterior products with a fundamental cycle are flat pullbacks along the projections

Let `X` and `Y` be schemes locally of finite type over the spectrum of a field, with `Y`
integral of dimension `d_Y`. The two projections of `X ×_k Y` are flat, so cycles pull back
along them, and the first clause of Stacks 0B0R says that these pullbacks are exterior products
with a fundamental cycle:

  `pr_X^*(α) = α × [Y]`  and  `pr_Y^*(β) = [X] × β`.

The base being the spectrum of a field is expressed by `Subsingleton C.S` and `IsIntegral C.S`,
the fundamental cycle `[Y]` is `Stacks.Chow.cycleAssociatedToClosedSubscheme C g (𝟙 Y) d`, and
the relative dimension of the projection is a hypothesis. Both identities are stated as
equalities of the underlying algebraic cycles.

## Main results

* `Stacks.Chow.flat_pointClosurePullback_snd`, `Stacks.Chow.flat_pointClosurePullback_fst` —
  over the spectrum of a field, the projection of the inverse image of a reduced point closure
  to the other factor is flat.
* `Stacks.Chow.flatPullbackFst_eq_exteriorProduct_fundamentalCycle` — clause (1) of Stacks 0B0R
  for the first projection: `pr_X^*(α) = α × [Y]`.
* `Stacks.Chow.flatPullbackSnd_eq_fundamentalCycle_exteriorProduct` — clause (1) of Stacks 0B0R
  for the second projection: `pr_Y^*(β) = [X] × β`.

## References

* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Flatness of the projections of a product with a point closure -/

/-- Over the spectrum of a field the projection `closure {x} ×_S Y ⟶ Y` is flat. -/
theorem flat_pointClosurePullback_snd {S X Y : Scheme.{u}} [Subsingleton S] [IsIntegral S]
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) :
    Flat (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
      pullback.snd f g) := by
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  have key : (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g =
      ((I.comapIso (pullback.fst f g)).hom ≫
        ((pullbackSymmetry (pullback.fst f g) I.subschemeι).trans
          (pullbackRightPullbackFstIso f g I.subschemeι)).hom) ≫
        pullback.snd (I.subschemeι ≫ f) g := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst I (pullback.fst f g)]
    simp [pullbackRightPullbackFstIso_hom_snd]
  rw [key]
  infer_instance

/-- Over the spectrum of a field the projection `X ×_S closure {y} ⟶ X` is flat. -/
theorem flat_pointClosurePullback_fst {S X Y : Scheme.{u}} [Subsingleton S] [IsIntegral S]
    (f : X ⟶ S) (g : Y ⟶ S) (y : Y) :
    Flat (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap (pullback.snd f g)).subschemeι ≫
      pullback.fst f g) := by
  set J : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))
  have key : (J.comap (pullback.snd f g)).subschemeι ≫ pullback.fst f g =
      ((J.comapIso (pullback.snd f g)).hom ≫
        (pullbackLeftPullbackSndIso f g J.subschemeι).hom) ≫
        pullback.fst f (J.subschemeι ≫ g) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst J (pullback.snd f g)]
    simp [pullbackLeftPullbackSndIso_hom_fst]
  rw [key]
  infer_instance

/-! ### Generic points of a product with a point closure -/

/-- The image of a generic point of the source of a flat morphism to an irreducible scheme is its
generic point. -/
private theorem base_genericPoints_eq_genericPoint {P Z : Scheme.{u}} (p : P ⟶ Z) [Flat p]
    [IrreducibleSpace Z] (ξ : genericPoints P) : p.base ξ.1 = genericPoint Z := by
  have hcomp := map_genericPoint_irreducibleComponent_eq_genericPoint p (genericPoints.component ξ)
  have hgen : (genericPoints.component ξ).2.1.genericPoint = ξ.1 :=
    ((genericPoints.component ξ).2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ (genericPoints.component ξ).2)).eq
      (genericPoints.isGenericPoint ξ)
  rwa [hgen] at hcomp

/-- A generic point of `closure {x} ×_S Y` lies over the generic point of the integral scheme
`Y`, the base being the spectrum of a field. -/
theorem snd_genericPoint_pointClosurePullback {S X Y : Scheme.{u}} [Subsingleton S]
    [IsIntegral S] (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral Y] (x : X)
    (ξ : genericPoints ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subscheme) :
    (pullback.snd f g).base
        (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι.base ξ.1) =
      genericPoint Y := by
  let _ := flat_pointClosurePullback_snd f g x
  simpa using base_genericPoints_eq_genericPoint
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
      pullback.snd f g) ξ

/-- A generic point of `X ×_S closure {y}` lies over the generic point of the integral scheme
`X`, the base being the spectrum of a field. -/
theorem fst_genericPoint_pointClosurePullback {S X Y : Scheme.{u}} [Subsingleton S]
    [IsIntegral S] (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] (y : Y)
    (ξ : genericPoints ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap (pullback.snd f g)).subscheme) :
    (pullback.fst f g).base
        (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).comap (pullback.snd f g)).subschemeι.base ξ.1) =
      genericPoint X := by
  let _ := flat_pointClosurePullback_fst f g y
  simpa using base_genericPoints_eq_genericPoint
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap (pullback.snd f g)).subschemeι ≫
      pullback.fst f g) ξ

/-! ### The exterior product ideal at a generic point -/

/-- At the generic point of a reduced irreducible `Y` the product of the two reduced closures is
all of `closure {x} ×_S Y`. -/
theorem exteriorProductIdeal_genericPoint_right {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsIntegral Y] (x : X) :
    exteriorProductIdeal f g x (genericPoint Y) =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g) := by
  have htop : Closeds.closure ({genericPoint Y} : Set Y) = ⊤ :=
    SetLike.coe_injective (genericPoint_spec Y)
  rw [exteriorProductIdeal, htop, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot, Scheme.IdealSheafData.comap_bot, sup_bot_eq]

/-- At the generic point of a reduced irreducible `X` the product of the two reduced closures is
all of `X ×_S closure {y}`. -/
theorem exteriorProductIdeal_genericPoint_left {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsIntegral X] (y : Y) :
    exteriorProductIdeal f g (genericPoint X) y =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap (pullback.snd f g) := by
  have htop : Closeds.closure ({genericPoint X} : Set X) = ⊤ :=
    SetLike.coe_injective (genericPoint_spec X)
  rw [exteriorProductIdeal, htop, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot, Scheme.IdealSheafData.comap_bot, bot_sup_eq]

/-- The cycle coefficient of a closed subscheme depends only on the ideal sheaf cutting it
out. -/
theorem closedSubschemeCycleCoeff_congr (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {I J : X.IdealSheafData} (h : I = J) (k : ℤ) (x : X) :
    closedSubschemeCycleCoeff C p I.subschemeι k x =
      closedSubschemeCycleCoeff C p J.subschemeι k x := by
  subst h
  rfl

/-- Along the generic point of an integral `Y` the exterior product multiplicity is the flat
pullback multiplicity of the first projection. -/
theorem exteriorProductWeight_genericPoint_right (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral Y]
    (j : ℤ) (z : (pullback f g : Scheme.{u})) :
    exteriorProductWeight C f g j ((pullback.fst f g).base z) (genericPoint Y) z =
      flatPullbackWeight C (pullback.fst f g ≫ f) (pullback.fst f g) j z :=
  closedSubschemeCycleCoeff_congr C (pullback.fst f g ≫ f)
    (exteriorProductIdeal_genericPoint_right f g ((pullback.fst f g).base z)) j z

/-- Along the generic point of an integral `X` the exterior product multiplicity is the flat
pullback multiplicity of the second projection. -/
theorem exteriorProductWeight_genericPoint_left (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral X]
    (j : ℤ) (z : (pullback f g : Scheme.{u})) :
    exteriorProductWeight C f g j (genericPoint X) ((pullback.snd f g).base z) z =
      flatPullbackWeight C (pullback.fst f g ≫ f) (pullback.snd f g) j z :=
  closedSubschemeCycleCoeff_congr C (pullback.fst f g ≫ f)
    (exteriorProductIdeal_genericPoint_left f g ((pullback.snd f g).base z)) j z

/-- The flat pullback multiplicity vanishes at a point whose image under `q` is not the point `η`
which every generic point of the inverse image of the reduced closure of its image maps to. -/
private theorem flatPullbackWeight_eq_zero_of_ne (C : ChowSituation.{u}) {P X Y : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (f : P ⟶ X) (q : P ⟶ Y) (η : Y) (j : ℤ) (z : P)
    (hgen : ∀ ξ : genericPoints ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({f.base z} : Set X))).comap f).subscheme,
      q.base (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({f.base z} : Set X))).comap f).subschemeι.base ξ.1) = η)
    (hz : q.base z ≠ η) : flatPullbackWeight C sP f j z = 0 := by
  rw [flatPullbackWeight, closedSubschemeCycleCoeff]
  split
  next hex =>
    obtain ⟨ξ, hξ, -⟩ := hex
    exact absurd (hξ ▸ hgen ξ) hz
  next => rfl

/-! ### Clause (1) of Stacks 0B0R -/

/-- **Clause (1) of Stacks 0B0R, first projection, over a general Chow situation.** The flat
pullback of an `r`-cycle `α` on `X` along `pr_X : X ×_S Y ⟶ X` is the exterior product `α × [Y]`
of `α` with the fundamental cycle of the integral scheme `Y`, the base being the spectrum of a
field. -/
theorem flatPullbackFst_eq_exteriorProduct_fundamentalCycle (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] {X Y : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral Y] (d : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension (pullback.fst f g) d)
    (hd : relativeDimension C.dimensionFunction g (genericPoint Y) = (d : ℤ)) (r : ℤ)
    (α : CycleGroup C f r) :
    (flatPullback C (pullback.fst f g ≫ f) f (pullback.fst f g) rfl d hrel r α).1 =
      (exteriorProduct C f g r (d : ℤ) α
        (cycleAssociatedToClosedSubscheme C g (𝟙 Y) (d : ℤ))).1 := by
  ext z
  rw [show (flatPullback C (pullback.fst f g ≫ f) f (pullback.fst f g) rfl d hrel r α).1 z =
    α.1 ((pullback.fst f g).base z) *
      flatPullbackWeight C (pullback.fst f g ≫ f) (pullback.fst f g) (r + (d : ℤ)) z from rfl,
    show (exteriorProduct C f g r (d : ℤ) α
        (cycleAssociatedToClosedSubscheme C g (𝟙 Y) (d : ℤ))).1 z =
      α.1 ((pullback.fst f g).base z) *
        (cycleAssociatedToClosedSubscheme C g (𝟙 Y) (d : ℤ)).1 ((pullback.snd f g).base z) *
        exteriorProductWeight C f g (r + (d : ℤ)) ((pullback.fst f g).base z)
          ((pullback.snd f g).base z) z from rfl]
  by_cases hz : (pullback.snd f g).base z = genericPoint Y
  · have hone : (cycleAssociatedToClosedSubscheme C g (𝟙 Y) (d : ℤ)).1
        ((pullback.snd f g).base z) = 1 := by
      rw [hz]
      exact cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint C g (𝟙 Y) (d : ℤ)
        (by simpa using hd)
    rw [hone, mul_one, hz, exteriorProductWeight_genericPoint_right]
  · have hzero : (cycleAssociatedToClosedSubscheme C g (𝟙 Y) (d : ℤ)).1
        ((pullback.snd f g).base z) = 0 :=
      cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne C g (𝟙 Y) (d : ℤ)
        (by simpa using hz)
    rw [hzero, mul_zero, zero_mul]
    rw [flatPullbackWeight_eq_zero_of_ne C _ (pullback.fst f g) (pullback.snd f g)
      (genericPoint Y) _ z (snd_genericPoint_pointClosurePullback f g _) hz, mul_zero]

/-- **Clause (1) of Stacks 0B0R, second projection, over a general Chow situation.** The flat
pullback of an `s`-cycle `β` on `Y` along `pr_Y : X ×_S Y ⟶ Y` is the exterior product `[X] × β`
of the fundamental cycle of the integral scheme `X` with `β`, the base being the spectrum of a
field. -/
theorem flatPullbackSnd_eq_fundamentalCycle_exteriorProduct (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] {X Y : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral X] (d : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension (pullback.snd f g) d)
    (hd : relativeDimension C.dimensionFunction f (genericPoint X) = (d : ℤ)) (s : ℤ)
    (β : CycleGroup C g s) :
    (flatPullback C (pullback.fst f g ≫ f) g (pullback.snd f g) pullback.condition.symm d hrel s
        β).1 =
      (exteriorProduct C f g (d : ℤ) s
        (cycleAssociatedToClosedSubscheme C f (𝟙 X) (d : ℤ)) β).1 := by
  ext z
  rw [show (flatPullback C (pullback.fst f g ≫ f) g (pullback.snd f g) pullback.condition.symm d
        hrel s β).1 z =
    β.1 ((pullback.snd f g).base z) *
      flatPullbackWeight C (pullback.fst f g ≫ f) (pullback.snd f g) (s + (d : ℤ)) z from rfl,
    show (exteriorProduct C f g (d : ℤ) s
        (cycleAssociatedToClosedSubscheme C f (𝟙 X) (d : ℤ)) β).1 z =
      (cycleAssociatedToClosedSubscheme C f (𝟙 X) (d : ℤ)).1 ((pullback.fst f g).base z) *
        β.1 ((pullback.snd f g).base z) *
        exteriorProductWeight C f g ((d : ℤ) + s) ((pullback.fst f g).base z)
          ((pullback.snd f g).base z) z from rfl]
  by_cases hz : (pullback.fst f g).base z = genericPoint X
  · have hone : (cycleAssociatedToClosedSubscheme C f (𝟙 X) (d : ℤ)).1
        ((pullback.fst f g).base z) = 1 := by
      rw [hz]
      exact cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint C f (𝟙 X) (d : ℤ)
        (by simpa using hd)
    rw [hone, one_mul, hz, add_comm (d : ℤ) s, exteriorProductWeight_genericPoint_left]
  · have hzero : (cycleAssociatedToClosedSubscheme C f (𝟙 X) (d : ℤ)).1
        ((pullback.fst f g).base z) = 0 :=
      cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne C f (𝟙 X) (d : ℤ)
        (by simpa using hz)
    rw [hzero, zero_mul, zero_mul]
    rw [flatPullbackWeight_eq_zero_of_ne C _ (pullback.snd f g) (pullback.fst f g)
      (genericPoint X) _ z (fst_genericPoint_pointClosurePullback f g _) hz, mul_zero]

end Stacks.Chow

end
