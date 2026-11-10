module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FundamentalClassMotive
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClassAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClassMul
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataCoordinates
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealization
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateTensorHom
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiUnitTwistTraceMonObj
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorCohomology
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorKunneth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The Weil data of a realization of motives

Let `k` be a field, `F` a field of characteristic `0`, and `G : M_k ⥤ graded F-vector spaces` a
`ℚ`-linear functor of symmetric monoidal categories with `G(𝟏(1))` nonzero only in degree `-2`
(`Stacks.WeilCohomology.WeilRealization`). Following the proof of Stacks 0FHK (and of 0FH1):

* (D0) `F(1) = G^{-2}(𝟏(1))`;
* (D1) `H^*(X) = G(h(X))`, the graded algebra of the commutative monoid `h(X)` (multiplication
  `[Γ_Δ]`), with pullbacks `G(h(f))`;
* (D2) `γ(α) = G(a_α)(e_{-i})` for `a_α : 𝟏(-i) ⟶ h(X)` the correspondence of `α`;
* (D3) `∫_X x = G([X])(x ⊗ e_d)` for `[X] : h(X) ⊗ 𝟏(d) ⟶ 𝟏` the fundamental class,

where `e_n ∈ G^{-2n}(𝟏(n))` are compatible generators. The twist by `F(m)` is read in coordinates.

The axioms follow as in the proof of Stacks 0FHK: (A) from the duality `h(X) ⊗ 𝟏(d)` of `h(X)`
(Stacks 0FGI) and the duality of graded vector spaces (Stacks 0FFV), (B) from
`h(X) ⊗ h(Y) ≅ h(X × Y)` and the multiplicativity of fundamental classes, and (C) from the
compatibilities of the correspondences `a_α` (Stacks 0FG0, 0FG5, 0FG8).

## Main definitions

* `Stacks.WeilCohomology.WeilRealization.toWeilData`: the data (D0)–(D3).
* `Stacks.WeilCohomology.WeilRealization.toWeilDataAxioms`: the data with axioms (A), (B), (C)
  (Stacks 0FHK).

## Main results

* `Stacks.WeilCohomology.WeilRealization.poincareDuality`: axiom (A).
* `Stacks.WeilCohomology.WeilRealization.kunneth`: axiom (B).
* `Stacks.WeilCohomology.WeilRealization.cycleClassPullback`,
  `Stacks.WeilCohomology.WeilRealization.cycleClassPushforward`,
  `Stacks.WeilCohomology.WeilRealization.cycleClassMul`,
  `Stacks.WeilCohomology.WeilRealization.cycleClassPoint`: axiom (C).

## Implementation notes

The motive `h(X)` is spelled `TwistedKaroubi.ofObj (𝐎 X)` and only the generic monoidal structure
`TwistedKaroubi.monoidalCategory` of the twisted Karoubi envelope is used, as in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoid`. The functor of a
realization
is reread on the twisted Karoubi envelope (`WeilRealization.functorTK`), with its braided structure
(`WeilRealization.braidedTK`) over the generic instances.

## References

* [Stacks Project, Tag 0FHK](https://stacks.math.columbia.edu/tag/0FHK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CategoryTheory.GradedCategory Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilRealization

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (G : WeilRealization k F)

/-- The functor of a realization, on the twisted Karoubi envelope `M_k` is built as. -/
abbrev functorTK :
    TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj ⥤
      GradedObject ℤ (ModuleCat.{w} F) :=
  G.functor

/-- The braided structure of a realization over the generic monoidal structure of the twisted
Karoubi envelope. -/
@[instance_reducible]
def braidedTK : @Functor.Braided (TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj)
    _ TwistedKaroubi.monoidalCategory TwistedKaroubi.braidedCategory
    (GradedObject ℤ (ModuleCat.{w} F)) _ _ GradedObject.koszulBraidedCategory G.functorTK :=
  G.braided

/-- (D0) **The Tate line `F(1) = G^{-2}(𝟏(1))`.** -/
abbrev tateLine : Type w :=
  (G.functor.obj (ChowMotiveCat.tate k 1)) (-2)

/-- The Tate line `F(1)` is one-dimensional over `F`. -/
theorem finrank_tateLine : Module.finrank F G.tateLine = 1 :=
  ChowMotiveCat.finrank_tate_apply G.tate_degree 1

/-- A basis vector `e₁` of `F(1)`. -/
def tateBasis : G.tateLine :=
  (tateLineCoordinate G.finrank_tateLine).symm 1

/-- The basis vector `e₁` of `F(1)` is nonzero. -/
theorem tateBasis_ne_zero : G.tateBasis ≠ 0 := by
  simp [tateBasis]

section

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

local notation "𝐎" =>
  (GradedCompositionData.Obj.mk :
    CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
      CorrespondenceCategory _)

attribute [local instance] braidedTK

/-- The monoidal structure of `WeilRealization.functorTK`. -/
@[instance_reducible]
def monoidalTK : G.functorTK.Monoidal :=
  Functor.Braided.toMonoidal (self := G.braidedTK)

attribute [local instance] monoidalTK

/-- The compatible generators `e_n ∈ G^{-2n}(𝟏(n))` with `e_1 = e₁` (Stacks 0FH1, proof). -/
def tateGen (n : ℤ) : (G.functor.obj (ChowMotiveCat.tate k n)) (-2 * n) :=
  TwistedKaroubi.tateGen (G := G.functorTK) G.tate_degree G.tateBasis_ne_zero n

/-- Each generator `eₙ ∈ G^{-2n}(𝟏(n))` is nonzero. -/
theorem tateGen_ne_zero (n : ℤ) : G.tateGen n ≠ 0 :=
  TwistedKaroubi.tateGen_ne_zero G.tate_degree G.tateBasis_ne_zero n

/-- `e₀` is the unit of `G`. -/
theorem tateGen_zero_heq : G.tateGen 0 ≍ TwistedKaroubi.tateOne G.functorTK :=
  TwistedKaroubi.tateGen_zero_heq G.tate_degree G.tateBasis_ne_zero

/-- The generators are multiplicative: `eₙ eₘ = e_{n+m}`. -/
theorem tateMul_tateGen (n m : ℤ) :
    TwistedKaroubi.tateMul G.functorTK n m (n + m) rfl (-2 * n) (-2 * m) (-2 * (n + m)) (by ring)
      (G.tateGen n) (G.tateGen m) = G.tateGen (n + m) :=
  TwistedKaroubi.tateMul_tateGen G.tate_degree G.tateBasis_ne_zero n m

/-- (D1) **`H^*(X) = G(h(X))`**, as an externally graded algebra. -/
abbrev cohAlg (X : (SmoothProjectiveScheme k).FullSubcategory) : ExternallyGradedAlgebra.{w, w} F :=
  G.functorTK.cohomologyAlgebra (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))

/-- (D1) **The pullback `f^* = G(h(f))`.** -/
def cohPull {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    (G.cohAlg Y).Total →ₐ[F] (G.cohAlg X).Total :=
  G.functorTK.cohomologyMap (ChowMotiveCat.motMap f)

/-- `F(m)` in coordinates. -/
abbrev twCoord (V : Type w) [AddCommGroup V] [Module F V] (m : ℤ) :
    tateTwist F G.tateLine V m ≃ₗ[F] V :=
  tateTwistCoordinates (tateLineCoordinate G.finrank_tateLine) m

/-- (D2) **The cycle class map in coordinates**, `γ(α) = G(a_α)(e_{-i})`. -/
def cycleClassCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    codimensionChowGroup k X.obj.hom i →+ (G.cohAlg X).grade (2 * i) :=
  ((G.cohAlg X).gradeEquiv (2 * i)).symm.toLinearMap.toAddMonoidHom.comp
    (ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen X i)

/-- (D3) **The trace map in coordinates**, `∫_X x = G([X])(x ⊗ e_d)`. -/
def traceCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    (G.cohAlg X).grade (2 * (d : ℤ)) →ₗ[F] F :=
  G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
    (G.tateGen d) (2 * d) (by ring) ∘ₗ ((G.cohAlg X).gradeEquiv (2 * (d : ℤ))).toLinearMap

/-- **The data (D0)–(D3) of a realization** (Stacks 0FHK). -/
def toWeilData : WeilData k F where
  tate := G.tateLine
  finrank_tate := G.finrank_tateLine
  H X := (G.cohAlg X).Total
  grade X := (G.cohAlg X).grade
  graded_comm X i j a b ha hb := G.functorTK.cohomologyAlgebra_mul_comm _ i j a b ha hb
  pull f := G.cohPull f
  pull_id X := by
    simp only [cohPull, ChowMotiveCat.motMap_id, Functor.cohomologyMap_id]
  pull_comp f g := by
    simp only [cohPull, ← ChowMotiveCat.motMap_comp, Functor.cohomologyMap_comp]
  pull_grade f n a ha := G.functorTK.cohomologyMap_mem_grade _ n ha
  cycleClass X i := (G.twCoord _ i).symm.toLinearMap.toAddMonoidHom.comp (G.cycleClassCoord X i)
  trace X d hX := G.traceCoord X d hX ∘ₗ (G.twCoord _ d).toLinearMap

/-! ### Coordinates of the data -/

/-- In coordinates, the cycle class map of `toWeilData` is `cycleClassCoord`. -/
theorem toWeilData_cycleClassCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    G.toWeilData.cycleClassCoord X i α = G.cycleClassCoord X i α := by
  rw [WeilData.cycleClassCoord_apply]
  exact (G.twCoord _ i).apply_symm_apply _

/-- In coordinates, the trace map of `toWeilData` is `traceCoord`. -/
theorem toWeilData_traceCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    G.toWeilData.traceCoord X d hX = G.traceCoord X d hX := by
  refine LinearMap.ext fun x ↦ ?_
  exact congrArg (G.traceCoord X d hX)
    ((G.twCoord ((G.cohAlg X).grade (2 * (d : ℤ))) d).apply_symm_apply x)

/-- The cup product of `H^*(X)` is the product `gradedMonMul` of the monoid `G(h(X))`. -/
theorem gradeEquiv_cup (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ) (h : i + j = n)
    (a : (G.cohAlg X).grade i) (b : (G.cohAlg X).grade j) :
    (G.cohAlg X).gradeEquiv n (G.toWeilData.cup X i j n h a b) =
      Functor.gradedMonMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i j n h
        ((G.cohAlg X).gradeEquiv i a) ((G.cohAlg X).gradeEquiv j b) := by
  subst h
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨a, rfl⟩ := ((G.cohAlg X).mem_grade_iff _).1 ha
  obtain ⟨b, rfl⟩ := ((G.cohAlg X).mem_grade_iff _).1 hb
  rw [(G.cohAlg X).gradeEquiv_apply ⟨_, ha⟩ a rfl, (G.cohAlg X).gradeEquiv_apply ⟨_, hb⟩ b rfl]
  exact (G.cohAlg X).gradeEquiv_apply _ _ ((G.cohAlg X).of_mul_of a b)

/-- The coordinate trace of a cup product is the graded trace of the monoid product in
`G(h(X))`. -/
private theorem traceCoord_cup (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * (d : ℤ))
    (a : (G.cohAlg X).grade i) (b : (G.cohAlg X).grade j) :
    G.toWeilData.traceCoord X d hX (G.toWeilData.cup X i j _ h a b) =
      G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
        (G.tateGen d) (2 * d) (by ring)
        (Functor.gradedMonMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i j (2 * d) h
          ((G.cohAlg X).gradeEquiv i a) ((G.cohAlg X).gradeEquiv j b)) := by
  rw [toWeilData_traceCoord]
  exact congrArg (G.functorTK.gradedTrace _ _ _ _) (G.gradeEquiv_cup X i j _ h a b)

/-! ### Axiom (A) -/

/-- Each graded piece `H^i(X)` of the data of a realization is finite-dimensional. -/
theorem finiteDimensionality : G.toWeilData.FiniteDimensionality := by
  intro X d hX i
  let := ChowMotiveCat.exactPairingMotive hX.relativeDimension
  have : FiniteDimensional F ((G.cohAlg X).piece i) :=
    Functor.finiteDimensional_of_exactPairing G.functorTK
    (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
    (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
      TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) i
  exact LinearEquiv.finiteDimensional ((G.cohAlg X).gradeEquiv i).symm

/-- For `X` equidimensional of dimension `d` and `i + j = 2d`, the pairing
`H^i(X) × H^j(X) → F`, `(a, b) ↦ ∫_X a ∪ b`, is perfect. -/
theorem perfectPairing : G.toWeilData.PerfectPairing := by
  refine WeilData.perfectPairing_of_coord _ fun X d hX i j hij ↦ ?_
  let := ChowMotiveCat.exactPairingMotive hX.relativeDimension
  have hP := Functor.isPerfPair_gradedTrace_gradedMonMul G.functorTK
    (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
    (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
    (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
    (ChowMotiveCat.evaluation_exactPairingMotive hX.relativeDimension) (s := -2 * d)
    ⟨-d, by ring⟩ (fun i hi ↦ ChowMotiveCat.isZero_tate_apply G.tate_degree d i hi)
    (G.tateGen_ne_zero d) (ChowMotiveCat.finrank_tate_apply G.tate_degree d) i j (2 * d) hij
    (by ring)
  have heq : (G.toWeilData.cup X i j _ hij).compr₂ (G.toWeilData.traceCoord X d hX) =
      ((Functor.gradedMonMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i j (2 * d)
        hij).compr₂ (G.functorTK.gradedTrace
          (ChowMotiveCat.fundamentalClassMot hX.relativeDimension) (G.tateGen d) (2 * d)
          (by ring))).compl₁₂
        ((G.cohAlg X).gradeEquiv i).toLinearMap ((G.cohAlg X).gradeEquiv j).toLinearMap := by
    refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
    exact G.traceCoord_cup X d hX i j hij a b
  rw [heq]
  exact LinearMap.IsPerfPair.compl₁₂ _ _ _

/-- **Axiom (A), Poincaré duality.** -/
theorem poincareDuality : G.toWeilData.PoincareDuality :=
  ⟨G.finiteDimensionality, G.perfectPairing⟩

/-! ### Axiom (B)(a) -/

/-- **Axiom (B)(a)**: the Künneth map `H^*(X) ⊗ H^*(Y) → H^*(X × Y)`,
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, is bijective. -/
theorem kunnethIsomorphism : G.toWeilData.KunnethIsomorphism := by
  intro X Y
  have := ChowMotiveCat.isIso_motMap_fst_snd_mul X Y
  refine Functor.bijective_of_gradedMonMul_map_map
    (ChowMotiveCat.motMap (CorrespondenceCategory.tensorFst X Y))
    (ChowMotiveCat.motMap (CorrespondenceCategory.tensorSnd X Y)) (G.toWeilData.kunnethMap X Y)
    fun i j a b ↦ ?_
  change G.cohPull _ (DirectSum.of (G.cohAlg X).piece i a) *
    G.cohPull _ (DirectSum.of (G.cohAlg Y).piece j b) = _
  refine (congrArg₂ (· * ·) (G.functorTK.cohomologyMap_of _ i a)
    (G.functorTK.cohomologyMap_of _ j b)).trans ?_
  refine ((G.cohAlg (SmoothProjectiveScheme.prod X Y)).of_mul_of _ _).trans ?_
  exact (DirectSum.lof_eq_of F _ _ _ _).symm

/-! ### Axiom (C)(a) -/

/-- **Axiom (C)(a)**: the cycle class map commutes with pullbacks, `γ(f^*β) = f^*γ(β)`. -/
theorem cycleClassPullback : G.toWeilData.CycleClassPullback := by
  refine WeilData.cycleClassPullback_of_coord _ fun {X Y} f i β ↦ ?_
  rw [toWeilData_cycleClassCoord, toWeilData_cycleClassCoord]
  refine Subtype.ext ?_
  change ((G.cohAlg X).gradeEquiv (2 * i)).symm _ =
    (G.cohPull f : _ → _) (((G.cohAlg Y).gradeEquiv (2 * i)).symm _)
  rw [ExternallyGradedAlgebra.gradeEquiv_symm_apply_coe,
    ExternallyGradedAlgebra.gradeEquiv_symm_apply_coe, cohPull, Functor.cohomologyMap_of]
  congr 1
  exact (ChowMotiveCat.cycleClassMotive_gysin G.functorTK G.tateGen f i β).symm

/-! ### Axiom (B)(b) -/

/-- On `H^n`, the pullback `f^*` is the degree-`n` component of `G(h(f))`. -/
theorem gradeEquiv_pullDeg {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (a : (G.cohAlg Y).grade n) :
    (G.cohAlg X).gradeEquiv n (G.toWeilData.pullDeg f n a) =
      G.functorTK.map (ChowMotiveCat.motMap f) n ((G.cohAlg Y).gradeEquiv n a) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨a, rfl⟩ := ((G.cohAlg Y).mem_grade_iff _).1 ha
  rw [(G.cohAlg Y).gradeEquiv_apply ⟨_, ha⟩ a rfl]
  exact (G.cohAlg X).gradeEquiv_apply _ _ (G.functorTK.cohomologyMap_of _ n a)

/-- **The trace of `pr₁^*a ∪ pr₂^*b`** on `X × Y`: `∫_X a · ∫_Y b` on the Künneth component
`H^{2d}(X) ⊗ H^{2e}(Y)`, and `0` on the others. -/
theorem traceCoord_cup_pullDeg (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d e : ℕ)
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hXY : IsNonemptyEquidimensional (SmoothProjectiveScheme.prod X Y) (d + e)) (i j : ℤ)
    (h : i + j = 2 * ((d + e : ℕ) : ℤ)) (a : (G.cohAlg X).grade i) (b : (G.cohAlg Y).grade j) :
    G.toWeilData.traceCoord _ (d + e) hXY (G.toWeilData.cup _ i j _ h
        (G.toWeilData.pullDeg (SmoothProjectiveScheme.fst X Y) i a)
        (G.toWeilData.pullDeg (SmoothProjectiveScheme.snd X Y) j b)) =
      if hi : i + -2 * (d : ℤ) = 0 then
        G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
            (G.tateGen d) i hi ((G.cohAlg X).gradeEquiv i a) *
          G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hY.relativeDimension)
            (G.tateGen e) j (by push_cast at h; omega) ((G.cohAlg Y).gradeEquiv j b)
      else 0 := by
  refine (G.traceCoord_cup _ (d + e) hXY i j h _ _).trans ?_
  rw [gradeEquiv_pullDeg, gradeEquiv_pullDeg]
  exact Functor.gradedTrace_gradedMonMul_map_map
    (ChowMotiveCat.motMap (CorrespondenceCategory.tensorFst X Y))
    (ChowMotiveCat.motMap (CorrespondenceCategory.tensorSnd X Y))
    (TwistedKaroubi.tateTensorHom (R := ℚ) (C := (canonicalCorrespondenceCompositionData k).Obj)
      d e ((d + e : ℕ) : ℤ) (by push_cast; ring))
    _ _ _ (ChowMotiveCat.fundamentalClassMot_tensor hX.relativeDimension hY.relativeDimension
      hXY.relativeDimension) ⟨-d, by ring⟩ (by push_cast; ring) _ _ _
    (TwistedKaroubi.tateGen_eq_map_tateTensorHom G.tate_degree G.tateBasis_ne_zero _ _ _ _ _)
    i j _ h (by push_cast; ring) _ _

/-- **Axiom (B)(b)**: `∫_{X × Y} pr₁^*a ∪ pr₂^*b = ∫_X a · ∫_Y b` for `a ∈ H^{2d}(X)` and
`b ∈ H^{2e}(Y)`, and the trace vanishes on the other Künneth components. -/
theorem kunnethTrace : G.toWeilData.KunnethTrace := by
  refine WeilData.kunnethTrace_of_coord _ fun X Y d e hX hY hXY ↦
    ⟨fun a b ↦ ?_, fun i j h hi a b ↦ ?_⟩
  · refine (G.traceCoord_cup_pullDeg X Y d e hX hY hXY _ _ _ a b).trans ?_
    rw [dite_eq_left (by ring), toWeilData_traceCoord, toWeilData_traceCoord]
    rfl
  · refine (G.traceCoord_cup_pullDeg X Y d e hX hY hXY _ _ h a b).trans ?_
    rw [dite_eq_right (by omega)]

/-- **Axiom (B), the Künneth formula.** -/
theorem kunneth : G.toWeilData.Kunneth :=
  ⟨G.kunnethIsomorphism, G.kunnethTrace⟩

/-! ### Axiom (C) from its motive-level form -/

/-- In `G(h(X))`, the cycle class `γ(α)` of `α` of codimension `i` is `G(a_α)(e_{-i})`. -/
theorem gradeEquiv_cycleClassCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    (G.cohAlg X).gradeEquiv (2 * i) (G.cycleClassCoord X i α) =
      ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen X i α :=
  ((G.cohAlg X).gradeEquiv (2 * i)).apply_symm_apply _

/-- Axiom (C)(c) for a realization, from `γ(α · β) = γ(α) γ(β)` in `G(h(X))`. -/
theorem cycleClassMul_of_motive
    (h : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
      (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j),
      ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen X (i + j)
          (codimensionIntersectionProduct k X.obj.hom i j α β) =
        Functor.gradedMonMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) (2 * i) (2 * j)
          (2 * (i + j)) (by ring) (ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen X i α)
          (ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen X j β)) :
    G.toWeilData.CycleClassMul := by
  refine WeilData.cycleClassMul_of_coord _ fun X i j α β ↦ ?_
  rw [toWeilData_cycleClassCoord, toWeilData_cycleClassCoord, toWeilData_cycleClassCoord]
  apply ((G.cohAlg X).gradeEquiv (2 * (i + j))).injective
  refine (G.gradeEquiv_cycleClassCoord X _ _).trans ((h X i j α β).trans ?_)
  refine Eq.trans ?_ (G.gradeEquiv_cup X _ _ _ _ _ _).symm
  rw [gradeEquiv_cycleClassCoord, gradeEquiv_cycleClassCoord]

/-- Axiom (C)(d) for a realization, from `∫_{Spec k} γ([Spec k]) = 1` in `G(h(Spec k))`. -/
theorem cycleClassPoint_of_motive
    (h : G.functorTK.gradedTrace
      (ChowMotiveCat.fundamentalClassMot isNonemptyEquidimensional_point.relativeDimension)
      (G.tateGen ((0 : ℕ) : ℤ)) (2 * ((0 : ℕ) : ℤ)) (by ring)
      (ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen (SmoothProjectiveScheme.point k) 0
        (fundamentalClass (SmoothProjectiveScheme.point k))) = 1) :
    G.toWeilData.CycleClassPoint := by
  refine WeilData.cycleClassPoint_of_coord _ ?_
  rw [toWeilData_traceCoord, toWeilData_cycleClassCoord]
  exact (congrArg (G.functorTK.gradedTrace _ _ _ _)
    (G.gradeEquiv_cycleClassCoord (SmoothProjectiveScheme.point k) 0 _)).trans h

/-- Axiom (C)(b) for a realization, from `∫_X f^*b · γ(α) = ∫_Y b · γ(f_*α)` in `G(h(X))`,
`G(h(Y))`. -/
theorem cycleClassPushforward_of_motive
    (h : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (d e : ℕ)
      (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (p q : ℤ)
      (hpq : q = p + e - d) (α : codimensionChowGroup k X.obj.hom p) (i : ℤ)
      (hi : i + 2 * p = 2 * d) (hi' : i + 2 * q = 2 * e)
      (b : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) i),
      G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
          (G.tateGen d) (2 * d) (by ring)
          (Functor.gradedMonMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i (2 * p)
            (2 * d) hi (G.functorTK.map (ChowMotiveCat.motMap f) i b)
            (ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen X p α)) =
        G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hY.relativeDimension)
          (G.tateGen e) (2 * e) (by ring)
          (Functor.gradedMonMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) i (2 * q)
            (2 * e) hi' b (ChowMotiveCat.cycleClassMotive G.functorTK G.tateGen Y q
              (equidimensionalPushforward f d e p q hpq α)))) :
    G.toWeilData.CycleClassPushforward G.perfectPairing := by
  refine WeilData.cycleClassPushforward_of_coord _ _
    fun {X Y} f d e hX hY p q hpq α i hi hi' b ↦ ?_
  change (G.cohAlg Y).grade i at b
  rw [toWeilData_cycleClassCoord, toWeilData_cycleClassCoord]
  refine (G.traceCoord_cup X d hX i _ hi _ _).trans
    (Eq.trans ?_ (G.traceCoord_cup Y e hY i _ hi' _ _).symm)
  rw [gradeEquiv_pullDeg, gradeEquiv_cycleClassCoord, gradeEquiv_cycleClassCoord]
  exact h f d e hX hY p q hpq α i hi hi' _

/-- **Axiom (C)(d)** for a realization. -/
theorem cycleClassPoint : G.toWeilData.CycleClassPoint :=
  G.cycleClassPoint_of_motive (ChowMotiveCat.gradedTrace_cycleClassMotive_point G.functorTK
    G.tateGen G.tateGen_zero_heq G.tateMul_tateGen)

/-- The generator `e_{-i}` read in degree `2i` (`ChowMotiveCat.tateGenNeg`) agrees with
`e_{-i} ∈ G^{2i}(𝟏(-i))` up to the identification of degrees. -/
theorem tateGenNeg_heq (i : ℤ) :
    ChowMotiveCat.tateGenNeg G.functorTK G.tateGen i ≍
      TwistedKaroubi.tateGen (G := G.functorTK) G.tate_degree G.tateBasis_ne_zero (-i) := by
  have key : ∀ {p q : ℤ} (h : p = q) (x : G.functorTK.obj (ChowMotiveCat.tate k (-i)) p),
      (eqToHom (congrArg (G.functorTK.obj (ChowMotiveCat.tate k (-i))) h)).hom x ≍ x := by
    intro p q h x
    subst h
    simp
  exact key (show -2 * -i = 2 * i by ring) (G.tateGen (-i))

/-- `e_{-(i+j)} = G(𝟏(-i) ⊗ 𝟏(-j) ⟶ 𝟏(-(i+j)))(e_{-i} · e_{-j})`, in the degrees `2i`, `2j`. -/
theorem tateGenNeg_add (i j : ℤ) :
    ChowMotiveCat.tateGenNeg G.functorTK G.tateGen (i + j) =
      G.functorTK.map (TwistedKaroubi.tateTensorHomOfEq (R := ℚ)
          (C := (canonicalCorrespondenceCompositionData k).Obj) (M := ChowMotiveCat.tate k (-i))
          (N := ChowMotiveCat.tate k (-j)) (P := ChowMotiveCat.tate k (-(i + j))) (-i) (-j)
          (-(i + j)) (by ring) rfl rfl rfl)
        (2 * (i + j)) (G.functorTK.gradedMul _ _ (2 * i) (2 * j) (2 * (i + j)) (by ring)
          (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen i)
          (ChowMotiveCat.tateGenNeg G.functorTK G.tateGen j)) :=
  TwistedKaroubi.eq_map_tateTensorHomOfEq_of_heq G.tate_degree G.tateBasis_ne_zero (-i) (-j)
    (-(i + j)) (by ring) rfl rfl rfl (by ring) (by ring) (by ring) (by ring) _ _ _
    (G.tateGenNeg_heq i) (G.tateGenNeg_heq j) (G.tateGenNeg_heq (i + j))

/-- Axiom (C)(c) for a realization, from `(a_α ⊗ a_β) ≫ μ = ψ ≫ a_{α·β}` on motives, where
`ψ : 𝟏(-i) ⊗ 𝟏(-j) ⟶ 𝟏(-(i + j))`. -/
theorem cycleClassMul_of_pointMotiveHom
    (h : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
      (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j),
      (ChowMotiveCat.pointMotiveHom X i α ⊗ₘ ChowMotiveCat.pointMotiveHom X j β) ≫
          MonObj.mul (X := TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) =
        TwistedKaroubi.tateTensorHomOfEq (R := ℚ)
            (C := (canonicalCorrespondenceCompositionData k).Obj) (M := ChowMotiveCat.tate k (-i))
            (N := ChowMotiveCat.tate k (-j)) (P := ChowMotiveCat.tate k (-(i + j))) (-i) (-j)
            (-(i + j)) (by ring) rfl rfl rfl ≫
          ChowMotiveCat.pointMotiveHom X (i + j)
            (codimensionIntersectionProduct k X.obj.hom i j α β)) :
    G.toWeilData.CycleClassMul :=
  G.cycleClassMul_of_motive fun X i j α β ↦
    (Functor.gradedMonMul_map_map_eq_map _ _ _ _ (h X i j α β) _ _ _ _
      (G.tateGenNeg_add i j)).symm

/-- **Axiom (C)(b)** for a realization. -/
theorem cycleClassPushforward : G.toWeilData.CycleClassPushforward G.perfectPairing :=
  G.cycleClassPushforward_of_motive fun f d e hX hY p q hpq α i hi hi' b ↦
    ChowMotiveCat.gradedTrace_gradedMonMul_cycleClassMotive_pushforward G.functorTK G.tateGen
      G.tateMul_tateGen f d e hX hY p q hpq α i hi hi' b

/-- **Axiom (C)(c)** for a realization. -/
theorem cycleClassMul : G.toWeilData.CycleClassMul :=
  G.cycleClassMul_of_pointMotiveHom fun X i j α β ↦ by
    convert ChowMotiveCat.pointMotiveHom_tensorHom_comp_mul X i j α β using 3

/-- **Axiom (C)**, compatibility with cycle classes, for a realization. -/
theorem cycleClassAxiom : G.toWeilData.CycleClassAxiom G.perfectPairing :=
  ⟨G.cycleClassPullback, G.cycleClassPushforward, G.cycleClassMul, G.cycleClassPoint⟩

end

/-- Let `k` be a field and `F` a field of characteristic `0`. A `ℚ`-linear functor
`G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories such that `G(𝟏(1))` is nonzero
only in degree `-2` (a `Stacks.WeilCohomology.WeilRealization`) gives data (D0)–(D3) satisfying
(A), (B) and (C): `F(1) = G^{-2}(𝟏(1))`, `H^*(X) = G(h(X))` with the cup product from the
multiplication `[Γ_Δ]` of `h(X)` and the pullbacks `G(h(f))`, the cycle class map
`γ(α) = G(a_α)(e_{-i})` and the trace map `∫_X x = G([X])(x ⊗ e_d)`
(`Stacks.WeilCohomology.WeilRealization.toWeilData`). -/
@[stacks 0FHK "a Q-linear functor G : M_k → graded F-vector spaces of symmetric monoidal \
categories with G(1(1)) nonzero only in degree -2 gives data (D0)-(D3) satisfying (A), (B), (C)"]
def toWeilDataAxioms : WeilDataAxioms k F where
  toWeilData := G.toWeilData
  poincareDuality := G.poincareDuality
  kunneth := G.kunneth
  cycleClassAxiom := G.cycleClassAxiom

/-- The data underlying `toWeilDataAxioms` is `toWeilData`. -/
@[simp]
theorem toWeilDataAxioms_toWeilData : G.toWeilDataAxioms.toWeilData = G.toWeilData :=
  rfl

end Stacks.WeilCohomology.WeilRealization

end
