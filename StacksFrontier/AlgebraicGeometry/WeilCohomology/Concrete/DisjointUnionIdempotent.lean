module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion

/-!
# The idempotents of a disjoint union

Let `Z = X ⨿ Y` be a disjoint union of smooth projective schemes over `k`, with coprojections
`i : X ⟶ Z` and `j : Y ⟶ Z`, and let `[X], [Y] ∈ CH^0(Z)` be the classes of the two open and
closed subschemes. The proof of Stacks 0FHJ uses that `i^![X] = [X]`, `i^![Y] = 0`,
`j^![X] = 0` and `j^![Y] = [Y]`, so that by axiom (C)(a) and Stacks 0FHF the cycle classes
`e = γ([X])` and `f = γ([Y])` in `H^0(Z)` restrict to `1` and `0` on `X` and to `0` and `1` on
`Y`. This file proves these facts, for any `X` and `Y`; no equidimensionality is assumed.

The Chow computations go through the Gysin map of an open immersion, which is restriction of
cycle classes (`Stacks.WeilCohomology.codimensionGysin_of_isOpenImmersion`). Restricted to `X`,
the cycle of the closed subscheme `X` of `Z` is the fundamental cycle of `X`, and restricted to
`Y` it vanishes, because the coefficients of the cycle of `X` are supported on the image of `X`.

## Main results

* `Stacks.WeilCohomology.codimensionGysin_closedSubschemeClass_self`,
  `Stacks.WeilCohomology.codimensionGysin_closedSubschemeClass_of_disjoint`: `i^![X] = [X]` and
  `j^![X] = 0` in `CH^0`.
* `Stacks.WeilCohomology.WeilData.pullTw_cycleClass_closedSubschemeClass_self`,
  `Stacks.WeilCohomology.WeilData.pullTw_cycleClass_closedSubschemeClass_of_disjoint`:
  `i^*γ([X]) = 1` and `j^*γ([X]) = 0`.

## References

* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

open SmoothProjectiveScheme

section Chow

variable {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z}

/-- Restricted to an open piece disjoint from a closed subscheme, the cycle of that closed
subscheme vanishes. -/
private theorem cycleGroupRestrict_cycleAssociatedToClosedSubscheme_eq_zero_of_disjoint
    {V : (SmoothProjectiveScheme k).FullSubcategory} (g : V ⟶ Z) [IsOpenImmersion g.hom.left]
    {A : Scheme.{u}} (ι : A ⟶ Z.obj.left) [IsClosedImmersion ι] (n : ℤ)
    (hd : Disjoint (Set.range g.hom.left.base) (Set.range ι.base)) :
    cycleGroupRestrict (fieldChowSituation k) Z.obj.hom V.obj.hom g.hom.left (Over.w g.hom) n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom ι n) = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [cycleGroupRestrict_apply]
  exact cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range_of_isOpenImmersion
    (fieldChowSituation k) Z.obj.hom (𝟙 _) ι ι (Category.comp_id _) n
    (fun ⟨a, ha⟩ ↦ hd.le_bot ⟨⟨y, rfl⟩, ⟨a, ha⟩⟩)

/-- Restricted to a piece, the cycle of that piece is its fundamental cycle. -/
theorem cycleGroupRestrict_cycleAssociatedToClosedSubscheme_self
    (hc : IsColimit (BinaryCofan.mk i j)) (n : ℤ) :
    haveI := isClosedImmersion_left_of_isColimit hc
    haveI := isOpenImmersion_left_of_isColimit hc
    cycleGroupRestrict (fieldChowSituation k) Z.obj.hom X.obj.hom i.hom.left (Over.w i.hom) n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom i.hom.left n) =
      fundamentalCycle (fieldChowSituation k) X.obj.hom n := by
  have := isClosedImmersion_left_of_isColimit hc
  have := isClosedImmersion_right_of_isColimit hc
  have := isOpenImmersion_left_of_isColimit hc
  have := isOpenImmersion_right_of_isColimit hc
  have hcompl := isCompl_range_of_isColimit hc
  have hsum := cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces
    (fieldChowSituation k) Z.obj.hom (𝟙 _) i.hom.left j.hom.left i.hom.left j.hom.left
    (Category.comp_id _) (Category.comp_id _) hcompl.disjoint hcompl.sup_eq_top n
  rw [← cycleGroupRestrict_fundamentalCycle (fieldChowSituation k) Z.obj.hom X.obj.hom
    i.hom.left (Over.w i.hom) n, fundamentalCycle, hsum, map_add]
  refine (add_eq_left.mpr ?_).symm
  exact cycleGroupRestrict_cycleAssociatedToClosedSubscheme_eq_zero_of_disjoint i j.hom.left n
    hcompl.disjoint

/-- Restricted to the other piece, the cycle of a piece vanishes. -/
theorem cycleGroupRestrict_cycleAssociatedToClosedSubscheme_of_disjoint
    (hc : IsColimit (BinaryCofan.mk i j)) (n : ℤ) :
    haveI := isClosedImmersion_left_of_isColimit hc
    haveI := isOpenImmersion_right_of_isColimit hc
    cycleGroupRestrict (fieldChowSituation k) Z.obj.hom Y.obj.hom j.hom.left (Over.w j.hom) n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom i.hom.left n) = 0 := by
  have := isClosedImmersion_left_of_isColimit hc
  have := isOpenImmersion_right_of_isColimit hc
  have hcompl := isCompl_range_of_isColimit hc
  exact cycleGroupRestrict_cycleAssociatedToClosedSubscheme_eq_zero_of_disjoint j i.hom.left n
    hcompl.disjoint.symm

/-- The Gysin map of an open immersion `g : V ⟶ Z` on the class of a closed subscheme `A` of `Z`,
part by part: on the part `V_d` it is the restriction to `V_d` of the restriction to `V` of the
cycle of `A`. -/
theorem codimensionGysin_closedSubschemeClass_apply {V : (SmoothProjectiveScheme k).FullSubcategory}
    (g : V ⟶ Z)
    [IsOpenImmersion g.hom.left] {A : Scheme.{u}} (ι : A ⟶ Z.obj.left) [IsClosedImmersion ι]
    (d : ℕ) :
    codimensionGysin V.obj.hom Z.obj.hom (Over.w g.hom) 0
        (closedSubschemeClass Z.obj.hom ι 0) d =
      chowGroupRestrict (fieldChowSituation k) V.obj.hom (partBase V.obj.hom d)
        (dimPart V.obj.hom d).ι rfl ((d : ℤ) - 0)
        (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) V.obj.hom _)
          (cycleGroupRestrict (fieldChowSituation k) Z.obj.hom V.obj.hom g.hom.left
            (Over.w g.hom) ((d : ℤ) - 0)
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Z.obj.hom ι
              ((d : ℤ) - 0)))) := by
  rw [codimensionGysin_of_isOpenImmersion, closedSubschemeClass_apply, chowGroupRestrict_comp,
    chowGroupRestrict_congr (j' := (dimPart V.obj.hom d).ι ≫ g.hom.left)
      (hjj' := dimPartMap_ι Z.obj.hom V.obj.hom (Over.w g.hom) d)
      (hj' := by rw [Category.assoc, Over.w g.hom]),
    ← chowGroupRestrict_mk, chowGroupRestrict_comp]
  rfl

/-- **`i^![X] = [X]`**: the Gysin map of the coprojection `i : X ⟶ X ⨿ Y` carries the class
`[X] ∈ CH^0(X ⨿ Y)` of the open and closed subscheme `X` to the fundamental class of `X`. -/
theorem codimensionGysin_closedSubschemeClass_self (hc : IsColimit (BinaryCofan.mk i j)) :
    haveI := isClosedImmersion_left_of_isColimit hc
    codimensionGysin X.obj.hom Z.obj.hom (Over.w i.hom) 0
        (closedSubschemeClass Z.obj.hom i.hom.left 0) = fundamentalClass X := by
  have := isClosedImmersion_left_of_isColimit hc
  have := isOpenImmersion_left_of_isColimit hc
  funext d
  rw [codimensionGysin_closedSubschemeClass_apply,
    cycleGroupRestrict_cycleAssociatedToClosedSubscheme_self hc, ← fundamentalChowClass,
    chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
  exact eq_of_heq ((fundamentalChowClass_heq _ _ (by ring)).trans
    (chowGroupDegreeEquiv_heq _ _ _ _).symm)

/-- **`j^![X] = 0`**: the Gysin map of the coprojection `j : Y ⟶ X ⨿ Y` kills the class
`[X] ∈ CH^0(X ⨿ Y)` of the other summand. -/
theorem codimensionGysin_closedSubschemeClass_of_disjoint (hc : IsColimit (BinaryCofan.mk i j)) :
    haveI := isClosedImmersion_left_of_isColimit hc
    codimensionGysin Y.obj.hom Z.obj.hom (Over.w j.hom) 0
        (closedSubschemeClass Z.obj.hom i.hom.left 0) = 0 := by
  have := isClosedImmersion_left_of_isColimit hc
  have := isOpenImmersion_right_of_isColimit hc
  funext d
  rw [codimensionGysin_closedSubschemeClass_apply,
    cycleGroupRestrict_cycleAssociatedToClosedSubscheme_of_disjoint hc, map_zero, map_zero]
  rfl

end Chow

/-- The coproduct cofan with its two coprojections exchanged is a coproduct cofan. -/
def isColimitSwap {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z}
    (hc : IsColimit (BinaryCofan.mk i j)) : IsColimit (BinaryCofan.mk j i) :=
  BinaryCofan.isColimitMk (fun s ↦ hc.desc (BinaryCofan.mk s.inr s.inl))
    (fun s ↦ hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.right⟩)
    (fun s ↦ hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩)
    (fun s _ h₁ h₂ ↦ BinaryCofan.IsColimit.hom_ext hc
      (h₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (h₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.right⟩).symm))


namespace SmoothProjectiveScheme

/-- The morphism `T ⟶ X × Y` with components `f` and `g`. -/
def prodLift {T X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : T ⟶ X)
    (g : T ⟶ Y) : T ⟶ prod X Y :=
  ObjectProperty.homMk (Over.homMk (U := T.obj) (V := (prod X Y).obj)
    (pullback.lift f.hom.left g.hom.left (by rw [Over.w f.hom, Over.w g.hom]))
    (by
      change pullback.lift f.hom.left g.hom.left _ ≫ pullback.fst _ _ ≫ X.obj.hom = T.obj.hom
      rw [pullback.lift_fst_assoc, Over.w f.hom]))

/-- The first component of `prodLift f g` is `f`. -/
@[reassoc (attr := simp)]
theorem prodLift_fst {T X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : T ⟶ X) (g : T ⟶ Y) :
    prodLift f g ≫ fst X Y = f :=
  hom_ext_left (pullback.lift_fst _ _ _)

/-- The second component of `prodLift f g` is `g`. -/
@[reassoc (attr := simp)]
theorem prodLift_snd {T X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : T ⟶ X) (g : T ⟶ Y) :
    prodLift f g ≫ snd X Y = g :=
  hom_ext_left (pullback.lift_snd _ _ _)

/-- Two morphisms into `X × Y` with the same components are equal. -/
theorem prod_hom_ext {T X Y : (SmoothProjectiveScheme k).FullSubcategory} {f g : T ⟶ prod X Y}
    (h₁ : f ≫ fst X Y = g ≫ fst X Y) (h₂ : f ≫ snd X Y = g ≫ snd X Y) : f = g :=
  hom_ext_left (pullback.hom_ext (congrArg (fun φ ↦ φ.hom.left) h₁)
    (congrArg (fun φ ↦ φ.hom.left) h₂))

/-- Two morphisms out of an empty smooth projective scheme are equal. -/
theorem hom_ext_of_isEmpty {T X : (SmoothProjectiveScheme k).FullSubcategory} [IsEmpty T.obj.left]
    (f g : T ⟶ X) : f = g :=
  hom_ext_left (isInitialOfIsEmpty.hom_ext _ _)

/-- A morphism of smooth projective schemes over `k` out of an empty one. -/
def homOfIsEmpty (T X : (SmoothProjectiveScheme k).FullSubcategory) [IsEmpty T.obj.left] : T ⟶ X :=
  ObjectProperty.homMk (Over.homMk (U := T.obj) (V := X.obj) (isInitialOfIsEmpty.to _)
    (isInitialOfIsEmpty.hom_ext _ _))

end SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

variable {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z}

/-- **`i^*γ([X]) = 1`**: the cycle class of the open and closed subscheme `X` of `X ⨿ Y`
restricts to the unit on `X`, by (C)(a), `i^![X] = [X]` and Stacks 0FHF. -/
theorem pullTw_cycleClass_closedSubschemeClass_self (hBa : W.KunnethIsomorphism)
    (hCa : W.CycleClassPullback) (hCc : W.CycleClassMul) (hCd : W.CycleClassPoint)
    (hc : IsColimit (BinaryCofan.mk i j)) :
    haveI := isClosedImmersion_left_of_isColimit hc
    W.pullTw i _ _ (W.cycleClass Z 0 (closedSubschemeClass Z.obj.hom i.hom.left 0)) =
      W.unitTw X 0 0 rfl := by
  have := isClosedImmersion_left_of_isColimit hc
  rw [← hCa, codimensionGysin_closedSubschemeClass_self hc]
  exact cycleClass_fundamentalClass hBa hCa hCc hCd X

/-- **`j^*γ([X]) = 0`**: the cycle class of the open and closed subscheme `X` of `X ⨿ Y` restricts
to zero on `Y`, by (C)(a) and `j^![X] = 0`. -/
theorem pullTw_cycleClass_closedSubschemeClass_of_disjoint (hCa : W.CycleClassPullback)
    (hc : IsColimit (BinaryCofan.mk i j)) :
    haveI := isClosedImmersion_left_of_isColimit hc
    W.pullTw j _ _ (W.cycleClass Z 0 (closedSubschemeClass Z.obj.hom i.hom.left 0)) = 0 := by
  have := isClosedImmersion_left_of_isColimit hc
  rw [← hCa, codimensionGysin_closedSubschemeClass_of_disjoint hc, map_zero]

/-- The idempotent `e = γ([X]) ∈ H^0(X ⨿ Y)`, as a class of the total cohomology. -/
def idempotentLeft (hc : IsColimit (BinaryCofan.mk i j)) : W.H Z :=
  haveI := isClosedImmersion_left_of_isColimit hc
  (W.twCoord Z _ _ (W.cycleClass Z 0 (closedSubschemeClass Z.obj.hom i.hom.left 0)) : W.H Z)

/-- The idempotent `idempotentLeft hc` restricts to `1` on `X` along `i`. -/
theorem pull_idempotentLeft_left (hBa : W.KunnethIsomorphism) (hCa : W.CycleClassPullback)
    (hCc : W.CycleClassMul) (hCd : W.CycleClassPoint) (hc : IsColimit (BinaryCofan.mk i j)) :
    W.pull i (idempotentLeft (W := W) hc) = 1 := by
  have := isClosedImmersion_left_of_isColimit hc
  have h := congrArg (fun y ↦ (W.twCoord X _ _ y : W.H X))
    (pullTw_cycleClass_closedSubschemeClass_self hBa hCa hCc hCd hc)
  rw [twCoord_pullTw, coe_pullDeg] at h
  exact h.trans (W.coe_twCoord_unitTw X 0 0 rfl)

/-- The idempotent `idempotentLeft hc` restricts to `0` on `Y` along `j`. -/
theorem pull_idempotentLeft_right (hCa : W.CycleClassPullback)
    (hc : IsColimit (BinaryCofan.mk i j)) :
    W.pull j (idempotentLeft (W := W) hc) = 0 := by
  have := isClosedImmersion_left_of_isColimit hc
  have h := congrArg (fun y ↦ (W.twCoord Y _ _ y : W.H Y))
    (pullTw_cycleClass_closedSubschemeClass_of_disjoint (W := W) hCa hc)
  rw [twCoord_pullTw, coe_pullDeg, map_zero, ZeroMemClass.coe_zero] at h
  exact h

/-- **The pair of restrictions is surjective once each restriction is**: for `b = i^*a` and
`c = j^*a'`, the class `a ∪ e + a' ∪ f` restricts to `(b, c)`, where `e = γ([X])` and
`f = γ([Y])`. This is the corresponding step of the source's proof of Stacks 0FHJ. -/
theorem pull_prod_surjective_of_surjective (hBa : W.KunnethIsomorphism)
    (hCa : W.CycleClassPullback) (hCc : W.CycleClassMul) (hCd : W.CycleClassPoint)
    (hc : IsColimit (BinaryCofan.mk i j)) (hi : Function.Surjective (W.pull i))
    (hj : Function.Surjective (W.pull j)) :
    Function.Surjective ((W.pull i).prod (W.pull j)) := by
  rintro ⟨b, c⟩
  obtain ⟨a, rfl⟩ := hi b
  obtain ⟨a', rfl⟩ := hj c
  set e := idempotentLeft (W := W) hc
  set f := idempotentLeft (W := W) (isColimitSwap hc)
  have h1 := pull_idempotentLeft_left hBa hCa hCc hCd hc
  have h2 := pull_idempotentLeft_right hCa hc
  have h3 := pull_idempotentLeft_left hBa hCa hCc hCd (isColimitSwap hc)
  have h4 := pull_idempotentLeft_right hCa (isColimitSwap hc)
  refine ⟨a * e + a' * f, ?_⟩
  rw [AlgHom.prod_apply, map_add, map_mul, map_mul, map_add, map_mul, map_mul, h1, h2, h3, h4,
    mul_one, mul_zero, add_zero, mul_zero, zero_add, mul_one]

/-- **Stacks Project, Tag 0FHF**, the empty case: `H^*(∅) = 0`. The proof is the source's idea,
that `H^*(∅) ⊗ H^*(Q) = H^*(∅ × Q) = H^*(∅)` by (B)(a), made explicit for
`Q = Spec k ⨿ Spec k`. The idempotent `e = γ([Spec k]) ∈ H^0(Q)` of the first summand restricts
to `1` and to `0` on the two summands. As `∅ × Q ⟶ ∅` is an isomorphism, `pr₂^*e = pr₁^*a` for
some `a ∈ H^*(∅)`, so `a ⊗ 1 = 1 ⊗ e` by (B)(a). Restricting the second factor to the two summands
gives `a ⊗ 1 = 1 ⊗ 1` and `a ⊗ 1 = 0` in `H^*(∅) ⊗ H^*(Spec k)`, hence `1 ⊗ 1 = 0`, and as
`H^*(Spec k) ≠ 0` (Stacks 0FHE), `1 = 0` in `H^*(∅)`. -/
@[stacks 0FHF "the empty case: H^*(∅) = 0, on the actual category of smooth projective schemes \
over k"]
theorem subsingleton_of_isEmpty (hBa : W.KunnethIsomorphism) (hCa : W.CycleClassPullback)
    (hCc : W.CycleClassMul) (hCd : W.CycleClassPoint)
        (E : (SmoothProjectiveScheme k).FullSubcategory)
    [IsEmpty E.obj.left] : Subsingleton (W.H E) := by
  set Q := coprodObj (point k) (point k)
  have hcQ := isColimitCoprodCofan (point k) (point k)
  set e : W.H Q := idempotentLeft (W := W) hcQ
  have he1 := pull_idempotentLeft_left hBa hCa hCc hCd hcQ
  have he2 := pull_idempotentLeft_right hCa hcQ
  have : IsEmpty (prod E Q).obj.left :=
    Function.isEmpty (fst E Q).hom.left.base
  -- the projection `E × Q ⟶ E` is an isomorphism
  have hφ : homOfIsEmpty E (prod E Q) ≫ fst E Q = 𝟙 E := hom_ext_of_isEmpty _ _
  have hφ' : fst E Q ≫ homOfIsEmpty E (prod E Q) = 𝟙 (prod E Q) := hom_ext_of_isEmpty _ _
  have hsurj : Function.Surjective (W.pull (fst E Q)) := fun y ↦
    ⟨W.pull (homOfIsEmpty E (prod E Q)) y, by
      rw [← AlgHom.comp_apply, ← W.pull_comp, hφ', W.pull_id, AlgHom.id_apply]⟩
  obtain ⟨a, ha⟩ := hsurj (W.pull (snd E Q) e)
  have htensor : a ⊗ₜ[F] (1 : W.H Q) = (1 : W.H E) ⊗ₜ[F] e := by
    apply (hBa E Q).1
    rw [kunnethMap_tmul, kunnethMap_tmul, map_one, map_one, mul_one, one_mul, ha]
  have hl := congrArg
    (LinearMap.lTensor (W.H E) (W.pull (coprodInl (point k) (point k))).toLinearMap) htensor
  have hr := congrArg
    (LinearMap.lTensor (W.H E) (W.pull (coprodInr (point k) (point k))).toLinearMap) htensor
  simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one] at hl hr
  rw [he1] at hl
  rw [he2, TensorProduct.tmul_zero] at hr
  have h0 : (1 : W.H E) ⊗ₜ[F] (1 : W.H (point k)) = 0 := hl.symm.trans hr
  have := nontrivial_point hCd
  obtain ⟨φ, hφ1⟩ : ∃ φ : Module.Dual F (W.H (point k)), φ 1 ≠ 0 := by
    by_contra! h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff F (1 : W.H (point k))).mp h)
  have h1 := congrArg ((TensorProduct.rid F (W.H E)).toLinearMap ∘ₗ
    (LinearMap.lTensor (W.H E) φ)) h0
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at h1
  have hone : (1 : W.H E) = 0 := by
    have := congrArg (fun y ↦ (φ 1)⁻¹ • y) h1
    simpa [smul_smul, inv_mul_cancel₀ hφ1] using this
  exact subsingleton_of_zero_eq_one hone.symm

end WeilData

end Stacks.WeilCohomology

end
