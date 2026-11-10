module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.AffineFamilies
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.ChartLocus
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.HilbertPresheaf

/-!
# The charts of the Hilbert scheme of points of an affine scheme

Let `X ⟶ S` be a morphism of affine schemes, `R = Γ(S)`, `A = Γ(X)` and `w : Fin d → A`. The
chart `F_w` of the degree-`d` Hilbert functor of `X` used in the proof of Stacks Tag 0B99
consists of the families `Z ⊆ X ×_S T` such that the images of the `w l` form a basis of
`(Z ⟶ T)_* 𝒪_Z`. This file constructs the scheme `C_w = Spec (chartRing R w)` and its universal
family, and identifies, over an affine base, the families lying in the chart with the
morphisms to `C_w`.

## Main definitions

* `Stacks.Hilbert.Chart.tensorHom`: for an affine `S`-scheme `T`, the isomorphism
  `Γ(T) ⊗_R A ≅ Γ(X ×_S T)`, as a ring map.
* `Stacks.Hilbert.Chart.familyKernel`: the ideal of `Γ(T) ⊗_R A` cutting out a family.
* `Stacks.Hilbert.Chart.IsChart`: the family lies in the chart attached to `w`.
* `Stacks.Hilbert.Chart.chartFamily`: the family attached to a chart function.
* `Stacks.Hilbert.Chart.chartScheme`, `Stacks.Hilbert.Chart.chartMap`: the chart and its map to
  the Hilbert presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace Stacks.Hilbert.Chart

variable {S : Scheme.{u}} [IsAffine S] (X : Over S) [IsAffine X.left] {d : ℕ}

/-- The algebra structure over `Γ(S)` on the global sections of an `S`-scheme. -/
abbrev baseAlgebra (T : Over S) : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra

attribute [local instance] baseAlgebra

/-- The fibre product `X ×_S T`. -/
abbrev ambient (T : Over S) : Scheme.{u} := ((Over.pullback T.hom).obj X).left

/-- The global sections of `X ×_S T` form the pushout of `Γ(S) → Γ(T)` and `Γ(S) → Γ(X)`. -/
theorem isPushout_ambient (T : Over S) [IsAffine T.left] :
    IsPushout T.hom.appTop X.hom.appTop
      (((Over.pullback T.hom).obj X).hom).appTop (pullback.fst X.hom T.hom).appTop :=
  (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback X.hom T.hom)).flip

/-- The isomorphism `Γ(T) ⊗_R A ≅ Γ(X ×_S T)` for an affine `S`-scheme `T`. -/
def tensorIso (T : Over S) [IsAffine T.left] :
    CommRingCat.of (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤)) ≅ Γ(ambient X T, ⊤) :=
  (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(T.left, ⊤) Γ(X.left, ⊤)).isoIsPushout _ _
    (isPushout_ambient X T)

/-- The ring map `Γ(T) ⊗_R A → Γ(X ×_S T)`, an isomorphism. -/
def tensorHom (T : Over S) [IsAffine T.left] :
    Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) →+* Γ(ambient X T, ⊤) :=
  (tensorIso X T).hom.hom

/-- The ring map `Γ(T) ⊗_R A → Γ(X ×_S T)` is bijective. -/
theorem tensorHom_bijective (T : Over S) [IsAffine T.left] :
    Function.Bijective (tensorHom X T) :=
  ConcreteCategory.bijective_of_isIso (tensorIso X T).hom

/-- `tensorHom` sends `r ⊗ 1` to the pullback of `r` along the projection `X ×_S T ⟶ T`. -/
theorem tensorHom_tmul_one (T : Over S) [IsAffine T.left] (r : Γ(T.left, ⊤)) :
    tensorHom X T (r ⊗ₜ 1) = (((Over.pullback T.hom).obj X).hom).appTop r :=
  congrArg (fun φ => φ.hom r) ((CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(T.left, ⊤)
    Γ(X.left, ⊤)).inl_isoIsPushout_hom _ _ (isPushout_ambient X T))

/-- `tensorHom` sends `1 ⊗ a` to the pullback of `a` along the projection `X ×_S T ⟶ X`. -/
theorem tensorHom_one_tmul (T : Over S) [IsAffine T.left] (a : Γ(X.left, ⊤)) :
    tensorHom X T (1 ⊗ₜ a) = (pullback.fst X.hom T.hom).appTop a :=
  congrArg (fun φ => φ.hom a) ((CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(T.left, ⊤)
    Γ(X.left, ⊤)).inr_isoIsPushout_hom _ _ (isPushout_ambient X T))

/-! ### Naturality of the tensor description -/

/-- `tensorHom` sends `r ⊗ a` to the product of the pullbacks of `r` and `a` to `X ×_S T`. -/
private theorem tensorHom_tmul (T : Over S) [IsAffine T.left] (r : Γ(T.left, ⊤))
    (a : Γ(X.left, ⊤)) :
    tensorHom X T (r ⊗ₜ a) = (((Over.pullback T.hom).obj X).hom).appTop r *
      (show Γ(ambient X T, ⊤) from (pullback.fst X.hom T.hom).appTop a) := by
  rw [show r ⊗ₜ[Γ(S, ⊤)] a = (r ⊗ₜ 1) * (1 ⊗ₜ a) by simp, map_mul, tensorHom_tmul_one,
    tensorHom_one_tmul]

/-- The `Γ(S)`-algebra map `Γ(T) → Γ(T')` induced by a morphism `T' ⟶ T` of `S`-schemes. -/
def appTopAlgHom {T' T : Over S} (g : T' ⟶ T) : Γ(T.left, ⊤) →ₐ[Γ(S, ⊤)] Γ(T'.left, ⊤) where
  toRingHom := g.left.appTop.hom
  commutes' r := by
    change g.left.appTop (T.hom.appTop r) = T'.hom.appTop r
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w g]

omit [IsAffine S] in
/-- `appTopAlgHom g` acts as the map on global sections induced by `g`. -/
@[simp]
theorem appTopAlgHom_apply {T' T : Over S} (g : T' ⟶ T) (r : Γ(T.left, ⊤)) :
    appTopAlgHom g r = g.left.appTop r :=
  rfl

/-- The map `Γ(T) ⊗_R A → Γ(T') ⊗_R A` induced by a morphism `T' ⟶ T`. -/
def tensorMap {T' T : Over S} (g : T' ⟶ T) :
    Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) →ₐ[Γ(S, ⊤)] Γ(T'.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) :=
  Algebra.TensorProduct.map (appTopAlgHom g) (AlgHom.id _ _)

/-- The isomorphisms `Γ(T) ⊗_R A ≅ Γ(X ×_S T)` are natural in the affine `S`-scheme `T`. -/
theorem tensorHom_comp_tensorMap {T' T : Over S} [IsAffine T.left] [IsAffine T'.left]
    (g : T' ⟶ T) :
    (tensorHom X T').comp (tensorMap X g).toRingHom =
      (familyBaseChangeMap X g).appTop.hom.comp (tensorHom X T) := by
  have h1 : ∀ r, (familyBaseChangeMap X g).appTop ((((Over.pullback T.hom).obj X).hom).appTop r) =
      (((Over.pullback T'.hom).obj X).hom).appTop (g.left.appTop r) := by
    intro r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, (isPullback_familyBaseChangeMap X g).w]
  have h2 : ∀ a, (familyBaseChangeMap X g).appTop ((pullback.fst X.hom T.hom).appTop a) =
      (pullback.fst X.hom T'.hom).appTop a := by
    intro a
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show familyBaseChangeMap X g ≫ pullback.fst X.hom T.hom = pullback.fst X.hom T'.hom by
        simp only [familyBaseChangeMap, pullback.lift_fst, pullback.map, Category.comp_id]]
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tensorMap,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, appTopAlgHom_apply]
    rw [tensorHom_tmul, tensorHom_tmul, map_mul, h1, h2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### The ideal of a family in the tensor description -/

variable {X}

/-- The ideal of `Γ(T) ⊗_R A` cutting out a family over an affine base. -/
def familyKernel {T : Over S} [IsAffine T.left] (Z : HilbertFamily X T d) :
    Ideal (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤)) :=
  Ideal.comap (tensorHom X T) (Z.ideal.ideal ⟨⊤, isAffineOpen_top _⟩)

/-- The image of `familyKernel Z` in `Γ(X ×_S T)` is the ideal of global sections of `Z`. -/
theorem map_familyKernel {T : Over S} [IsAffine T.left] (Z : HilbertFamily X T d) :
    Ideal.map (tensorHom X T) (familyKernel Z) = Z.ideal.ideal ⟨⊤, isAffineOpen_top _⟩ :=
  Ideal.map_comap_of_surjective _ (tensorHom_bijective X T).2 _

/-- The ideal of the base change of a family along `T' ⟶ T` is generated by the image of the ideal
of the family under `Γ(T) ⊗_R A → Γ(T') ⊗_R A`. -/
theorem familyKernel_baseChange {T' T : Over S} [IsAffine T.left] [IsAffine T'.left] (g : T' ⟶ T)
    (Z : HilbertFamily X T d) :
    familyKernel (baseChange X g Z) = Ideal.map (tensorMap X g) (familyKernel Z) := by
  have h := affineFamilyEquiv_baseChange X d g Z
  rw [affineFamilyEquiv_apply_coe, affineFamilyEquiv_apply_coe] at h
  rw [familyKernel, h, ← map_familyKernel Z, Ideal.map_map, ← tensorHom_comp_tensorMap,
    ← Ideal.map_map]
  exact Ideal.comap_map_of_bijective _ (tensorHom_bijective X T')

/-- A family over an affine base is determined by its ideal in `Γ(T) ⊗_R A`. -/
theorem familyKernel_injective {T : Over S} [IsAffine T.left] {Z Z' : HilbertFamily X T d}
    (h : familyKernel Z = familyKernel Z') : Z = Z' := by
  refine (affineFamilyEquiv X d T).injective (Subtype.ext ?_)
  rw [affineFamilyEquiv_apply_coe, affineFamilyEquiv_apply_coe, ← map_familyKernel Z,
    ← map_familyKernel Z', h]

/-! ### The quotient attached to a family -/

variable (X) in
/-- `Γ(T) ⊗_R A ≅ Γ(X ×_S T)` as an isomorphism of `Γ(T)`-algebras. -/
def tensorAlgEquiv (T : Over S) [IsAffine T.left] :
    letI := familyAlgebra X T
    (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤)) ≃ₐ[Γ(T.left, ⊤)] Γ(ambient X T, ⊤) :=
  letI := familyAlgebra X T
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (tensorHom X T) (tensorHom_bijective X T))
    fun r => by
      change tensorHom X T (algebraMap _ _ r) = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        tensorHom_tmul_one]
      rfl

variable (X) in
/-- `(Γ(T) ⊗_R A) / K ≅ Γ(X ×_S T) / K Γ(X ×_S T)`, linearly over `Γ(T)`. -/
def quotientTensorEquiv (T : Over S) [IsAffine T.left]
    (K : Ideal (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤))) :
    letI := familyAlgebra X T
    (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) ⧸ K) ≃ₗ[Γ(T.left, ⊤)]
      (Γ(ambient X T, ⊤) ⧸ Ideal.map (tensorHom X T) K) :=
  letI := familyAlgebra X T
  (Ideal.quotientEquivAlg K (Ideal.map (tensorHom X T) K) (tensorAlgEquiv X T) rfl).toLinearEquiv

variable (X) in
/-- The image in `Γ(X ×_S T)` of an ideal `K` of `Γ(T) ⊗_R A` cuts out a family exactly when
`(Γ(T) ⊗_R A) / K` is finite locally free of rank `d` over `Γ(T)`. -/
theorem isFamilyIdeal_map_iff (T : Over S) [IsAffine T.left]
    (K : Ideal (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤))) :
    IsFamilyIdeal X d T (Ideal.map (tensorHom X T) K) ↔
      Module.IsFiniteLocallyFreeOfRank Γ(T.left, ⊤) (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) ⧸ K) d :=
  ⟨fun h => h.of_linearEquiv (quotientTensorEquiv X T K).symm,
    fun h => h.of_linearEquiv (quotientTensorEquiv X T K)⟩

/-- The quotient `(Γ(T) ⊗_R A) / K_Z` attached to a family is finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_familyKernel {T : Over S} [IsAffine T.left]
    (Z : HilbertFamily X T d) :
    Module.IsFiniteLocallyFreeOfRank Γ(T.left, ⊤)
      (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) ⧸ familyKernel Z) d := by
  rw [← isFamilyIdeal_map_iff, map_familyKernel]
  exact (affineFamilyEquiv X d T Z).2

/-- The quotient `(Γ(T) ⊗_R A) / K_Z` attached to a family is a finite `Γ(T)`-module. -/
instance finite_familyKernel {T : Over S} [IsAffine T.left] (Z : HilbertFamily X T d) :
    Module.Finite Γ(T.left, ⊤) (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) ⧸ familyKernel Z) :=
  Module.IsFiniteLocallyFreeOfRank.finite (isFiniteLocallyFreeOfRank_familyKernel Z)

/-! ### Families in a chart -/

variable (w : Fin d → Γ(X.left, ⊤))

/-- **A family lies in the chart attached to `w`** when the images of the `w l` span the
quotient `(Γ(T) ⊗_R A) / K_Z`, i.e. span the global sections of the family over `T`. -/
def IsChart {T : Over S} [IsAffine T.left] (Z : HilbertFamily X T d) : Prop :=
  Submodule.span Γ(T.left, ⊤) (Set.range (chartVector w (familyKernel Z))) = ⊤

variable (X) in
/-- **The family attached to a chart function.** -/
def chartFamily (T : Over S) [IsAffine T.left] {t : Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤)}
    (ht : IsChartFunction Γ(S, ⊤) w t) : HilbertFamily X T d :=
  (affineFamilyEquiv X d T).symm ⟨Ideal.map (tensorHom X T) (chartIdeal Γ(S, ⊤) w t),
    (isFamilyIdeal_map_iff X T _).mpr (Module.isFiniteLocallyFreeOfRank_of_basis (chartBasis ht))⟩

variable (X) in
/-- The ideal of the chart family of `t` is the chart ideal of `t`. -/
theorem familyKernel_chartFamily (T : Over S) [IsAffine T.left]
    {t : Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤)} (ht : IsChartFunction Γ(S, ⊤) w t) :
    familyKernel (chartFamily X w T ht) = chartIdeal Γ(S, ⊤) w t := by
  rw [familyKernel, chartFamily]
  change Ideal.comap _ ((affineFamilyEquiv X d T) ((affineFamilyEquiv X d T).symm _)).1 = _
  rw [Equiv.apply_symm_apply]
  exact Ideal.comap_map_of_bijective _ (tensorHom_bijective X T)

variable (X) in
/-- The chart family of a chart function lies in the chart attached to `w`. -/
theorem isChart_chartFamily (T : Over S) [IsAffine T.left]
    {t : Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤)} (ht : IsChartFunction Γ(S, ⊤) w t) :
    IsChart w (chartFamily X w T ht) := by
  rw [IsChart, familyKernel_chartFamily]
  exact span_chartVector t

omit [IsAffine S] [IsAffine X.left] in
variable (X) in
/-- Composing a chart function with the map `Γ(T) → Γ(T')` induced by `T' ⟶ T` gives a chart
function. -/
theorem isChartFunction_comp_appTop {T' T : Over S} (g : T' ⟶ T)
    {t : Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤)} (ht : IsChartFunction Γ(S, ⊤) w t) :
    IsChartFunction Γ(S, ⊤) w fun l a => appTopAlgHom g (t l a) := by
  simpa using isChartFunction_comp (R := Γ(S, ⊤)) (w := w) ((appTopAlgHom g).comp (lift ht))

variable (X) in
/-- **Base change of a chart family is the chart family of the base-changed chart function.** -/
theorem baseChange_chartFamily {T' T : Over S} [IsAffine T.left] [IsAffine T'.left] (g : T' ⟶ T)
    {t : Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤)} (ht : IsChartFunction Γ(S, ⊤) w t) :
    baseChange X g (chartFamily X w T ht) =
      chartFamily X w T' (isChartFunction_comp_appTop X w g ht) := by
  apply familyKernel_injective
  rw [familyKernel_baseChange, familyKernel_chartFamily, familyKernel_chartFamily,
    chartIdeal_comp]
  rfl

/-- For a family in the chart attached to `w`, the map `Γ(T)^d → (Γ(T) ⊗_R A) / K_Z` given by the
images of the `w l` is bijective. -/
theorem chartSum_mk_surjective_of_isChart {T : Over S} [IsAffine T.left] {Z : HilbertFamily X T d}
    (h : IsChart w Z) : Function.Bijective (chartSum w (Ideal.Quotient.mk (familyKernel Z))) := by
  let φ := Fintype.linearCombination Γ(T.left, ⊤) (chartVector w (familyKernel Z))
  have hφ : ⇑φ = chartSum w (Ideal.Quotient.mk (familyKernel Z)) := by
    funext c
    rw [Fintype.linearCombination_apply, chartSum, sum_smul_chartVector]
  have hsurj : Function.Surjective φ := by
    rwa [← LinearMap.range_eq_top, Fintype.range_linearCombination]
  rw [← hφ]
  exact ⟨injective_of_surjective_of_isFiniteLocallyFreeOfRank
    (isFiniteLocallyFreeOfRank_familyKernel Z) φ hsurj, hsurj⟩

/-- The chart function of a family in the chart. -/
def chartFunctionOf {T : Over S} [IsAffine T.left] {Z : HilbertFamily X T d} (h : IsChart w Z) :
    Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤) :=
  chartCoords w (Ideal.Quotient.mk (familyKernel Z)) (chartSum_mk_surjective_of_isChart w h)

variable (X) in
/-- The chart function of a family in the chart is a chart function. -/
theorem isChartFunction_chartFunctionOf {T : Over S} [IsAffine T.left] {Z : HilbertFamily X T d}
    (h : IsChart w Z) : IsChartFunction Γ(S, ⊤) w (chartFunctionOf w h) :=
  isChartFunction_chartCoords _ _

variable (X) in
/-- **A family in the chart is the chart family of its chart function.** -/
theorem chartFamily_chartFunctionOf {T : Over S} [IsAffine T.left] {Z : HilbertFamily X T d}
    (h : IsChart w Z) :
    chartFamily X w T (isChartFunction_chartFunctionOf X w h) = Z := by
  apply familyKernel_injective
  rw [familyKernel_chartFamily, chartFunctionOf, ← ker_eq_chartIdeal_chartCoords, Ideal.mk_ker]

variable (X) in
/-- The chart function of the chart family of `t` is `t`. -/
theorem chartFunctionOf_chartFamily (T : Over S) [IsAffine T.left]
    {t : Fin d → Γ(X.left, ⊤) → Γ(T.left, ⊤)} (ht : IsChartFunction Γ(S, ⊤) w t) :
    chartFunctionOf w (isChart_chartFamily X w T ht) = t :=
  chartCoords_eq _ _ (by rw [Ideal.mk_ker, familyKernel_chartFamily])

/-! ### The locus of a chart -/

/-- The zeroth Fitting ideal of the cokernel of `Γ(T)^d → (Γ(T) ⊗_R A) / K_Z`: its zero locus is
the closed set over which the chart attached to `w` does not apply. -/
def chartFitting {T : Over S} [IsAffine T.left] (Z : HilbertFamily X T d) : Ideal Γ(T.left, ⊤) :=
  fittingIdeal (R := Γ(T.left, ⊤))
    (M := (Γ(T.left, ⊤) ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) ⧸ familyKernel Z) ⧸
      Submodule.span Γ(T.left, ⊤) (Set.range (chartVector w (familyKernel Z)))) 0

variable (X) in
/-- **The locus of a chart.** A base change of a family lies in the chart exactly when the
Fitting ideal `chartFitting w Z` extends to the unit ideal. -/
theorem isChart_baseChange_iff {T' T : Over S} [IsAffine T.left] [IsAffine T'.left] (g : T' ⟶ T)
    (Z : HilbertFamily X T d) :
    IsChart w (baseChange X g Z) ↔ Ideal.map g.left.appTop.hom (chartFitting w Z) = ⊤ := by
  rw [IsChart, familyKernel_baseChange]
  exact span_chartVector_map_eq_top_iff w (appTopAlgHom g) (familyKernel Z)

end Stacks.Hilbert.Chart

end
