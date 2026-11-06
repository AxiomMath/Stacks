module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankChartModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeGeometricPoint
public import StacksFrontier.RingTheory.Fitting.KernelRankStratum

/-!
# Bottom models and Fitting ideals

Let `K` be an object of `D(𝒪_U)` on the algebraic space represented by `U`, with a bottom model in
degree `a` whose differential `𝒪^n ⟶ 𝒪^m` is the matrix `A` over `Γ(U)`. For a morphism
`t : T ⟶ U` from an affine `T`, the derived pullback of `K` along `t` is universally of bottom
rank `r` exactly when, with `θ = t^* : Γ(U) → Γ(T)`, the Fitting ideals of `C_A = coker Aᵀ` satisfy
`θ(Fit_{r-1}) = 0` and `θ(Fit_r) Γ(T) = Γ(T)`. This is the content of Stacks 0BDL on a chart.

## Main results

* `AlgebraicGeometry.Space.BottomModel.isUniversallyFreeBottom_iff`: the Fitting description.
* `AlgebraicGeometry.Space.BottomRankLocus.isUniversallyFreeBottom_of_forall_chart`: being
  universally of bottom rank `r` is étale local on the source.
* `AlgebraicGeometry.Space.BottomModel.fittingIdeal_eq_top_of_forall_fieldValuedPoint` and
  `AlgebraicGeometry.Space.BottomModel.fittingIdeal_pred_eq_bot`: the two Fitting conditions from
  local freeness at field points and on `T`.
* `AlgebraicGeometry.Space.natCast_eq_of_isFiniteLocallyFreeOfIntRank_freeObj`: the rank of a free
  module on a nonempty algebraic space is its local rank.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open BottomRankLocus

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### General facts -/

/-- A free module `𝒪^{⊕r}` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfIntRank_freeObj (Y : AlgebraicSpaces B S hS) (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank (freeObjMatrixKernelSplitting (ringedToposUnit Y) r)
        (r : ℤ) := by
  refine (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS _ r).2 fun y => ?_
  obtain ⟨V, hV⟩ := exists_smallEtale_mem_range B S hS Y.2 y
  exact ⟨V, hV, r, rfl, ⟨freeObjMapIsoMatrixKernelSplitting (pb (chartToSpace B S hS Y V))
    (pbUnitIso (chartToSpace B S hS Y V)) r ≪≫
    (Stacks.SheafOfModules.freeULiftFinIsoBiproduct
      (structureSheaf B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2) r).symm⟩⟩

namespace BottomRankLocus

variable {X : AlgebraicSpaces B S hS}
  {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  {a : ℤ} {r : ℕ}

/-- Being universally of bottom rank `r` along `t ≫ φ` for `E` is being so along `t` for
`Lφ^*E`. -/
theorem isUniversallyFreeBottom_comp_iff {Y Y' : AlgebraicSpaces B S hS} (φ : Y ⟶ X)
    (t : Y' ⟶ Y) :
    IsUniversallyFreeBottom E a r (t ≫ φ) ↔
      IsUniversallyFreeBottom ((smallEtaleDerivedModulePullback B S hS φ).obj E) a r t := by
  have e : ∀ {Y'' : AlgebraicSpaces B S hS} (g : Y'' ⟶ Y'),
      pullbackHomology ((smallEtaleDerivedModulePullback B S hS φ).obj E) a (g ≫ t) ≅
        pullbackHomology E a (g ≫ t ≫ φ) := fun g =>
    (DerivedCategory.homologyFunctor _ a).mapIso
      ((smallEtaleDerivedModulePullbackCompIso B S hS (g ≫ t) φ).app E ≪≫
        (smallEtaleDerivedModulePullbackCongr B S hS (Category.assoc g t φ)).app E)
  exact ⟨fun h Y'' g => isFiniteLocallyFreeOfIntRank_of_iso B S hS (e g).symm (h Y'' g),
    fun h Y'' g => isFiniteLocallyFreeOfIntRank_of_iso B S hS (e g) (h Y'' g)⟩

/-- **Being universally of bottom rank `r` is étale local on the source.** -/
theorem isUniversallyFreeBottom_of_forall_chart {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (h : ∀ y : points B S hS Y.1, ∃ W : SmallEtale B S hS Y.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ∧
        IsUniversallyFreeBottom E a r (chartToSpace B S hS Y W ≫ f)) :
    IsUniversallyFreeBottom E a r f := by
  intro Y' g
  refine (isFiniteLocallyFreeOfIntRank_homology_iff_forall_chart B S hS (g ≫ f) E a r).2
    fun y => ?_
  obtain ⟨W, hW, hWf⟩ := h (pointsMap B S hS Y'.1 g.hom y)
  obtain ⟨T, k, hyT, hk⟩ := exists_smallEtale_chart_lift B S hS Y'.2 g.hom W y hW
  have hc : chartToSpace B S hS Y' T ≫ g =
      representedSpaceMap B S hS k ≫ chartToSpace B S hS Y W :=
    InducedCategory.hom_ext hk.symm
  have e : chartToSpace B S hS Y' T ≫ g ≫ f =
      representedSpaceMap B S hS k ≫ chartToSpace B S hS Y W ≫ f := by
    rw [← Category.assoc, hc]
    exact Category.assoc _ _ _
  exact ⟨T, hyT, isFiniteLocallyFreeOfIntRank_of_iso B S hS
    (eqToIso (congrArg (fun k => pullbackHomology E a k) e.symm))
    (hWf _ (representedSpaceMap B S hS k))⟩

end BottomRankLocus

namespace BottomModel

variable {Y : AlgebraicSpaces B S hS}
  {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} {a : ℤ}
  {R : Type u} [CommRing R] {ψ : R →+* End (ringedToposUnit Y)} {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) R}

/-- The cohomology in the bottom degree of an object with a bottom model is the kernel of the
matrix of the model. -/
def homologyIsoKernel (M : BottomModel K a ψ A) :
    (DerivedCategory.homologyFunctor _ a).obj K ≅
      kernel (matrixHomMatrixKernelSplitting (ringedToposUnit Y) ψ A) := by
  have := M.isStrictlyGE
  exact (DerivedCategory.homologyFunctor _ a).mapIso M.iso ≪≫
    (DerivedCategory.homologyFunctorFactors _ a).app M.P ≪≫
    (M.P.isoHomologyπ (a - 1) a (by simp)
      ((M.P.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)).symm ≪≫
    IsLimit.conePointUniqueUpToIso (M.P.cyclesIsKernel a (a + 1) (by simp))
      (kernelIsKernel (M.P.d a (a + 1))) ≪≫
    kernel.mapIso _ _ M.e₀ M.e₁ (by rw [M.d_eq]; simp)

end BottomModel

/-! ### Represented spaces -/

/-- The ring map `Γ(U) → End(𝒪_U)` on the algebraic space represented by `U`. -/
abbrev repRho (U : BigFppfOver B S hS) :=
  Stacks.SheafOfModules.unitEndRingHom.{u}
    (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (isTerminal_idChart B S hS U)

/-- The ring map `Γ(U) → End(𝒪_U)` is bijective. -/
theorem bijective_repRho (U : BigFppfOver B S hS) : Function.Bijective (repRho U) :=
  Stacks.SheafOfModules.bijective_unitEndRingHom.{u}
    (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (isTerminal_idChart B S hS U)

/-- The ring map `Γ(U) → Γ(T)` induced on endomorphisms of structure sheaves by pullback along
`t : T ⟶ U`; it is pullback of functions (`repTheta_apply`). -/
def repTheta {T U : BigFppfOver B S hS} (t : T ⟶ U) :=
  baseChangeRingHom.{u}
    (C := Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (D := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (R := (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj.obj
      (op (idChart B S hS U)))
    (R' := (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).obj.obj
      (op (idChart B S hS T)))
    (ρ := repRho U) (repRho T) (bijective_repRho T)
    (modulePullback B S hS (representedSpaceMap B S hS t))
    (hF := modulePullback_additive (representedSpaceMap B S hS t))
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS t))

/-- The map `repTheta t` is pullback of global functions along the morphism of schemes of `t`. -/
theorem repTheta_apply {T U : BigFppfOver B S hS} (t : T ⟶ U)
    (x : (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj.obj
      (op (idChart B S hS U))) :
    repTheta t x = ((BigFppfOver.toScheme B S hS).map t).appTop x :=
  baseChangeRingHom_representedSpaceMap B S hS t x

/-- The endomorphism of `𝒪_T` given by `repTheta t x` is the pullback along `t` of the
endomorphism of `𝒪_U` given by `x`. -/
theorem repTheta_spec {T U : BigFppfOver B S hS} (t : T ⟶ U)
    (x : (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj.obj
      (op (idChart B S hS U))) :
    (repRho T (repTheta t x)).asHom =
      (pbUnitIso (representedSpaceMap B S hS t)).inv ≫
        (pb (representedSpaceMap B S hS t)).map (repRho U x).asHom ≫
          (pbUnitIso (representedSpaceMap B S hS t)).hom :=
  map_baseChangeRingHom.{u} (ρ := repRho U) (repRho T) (bijective_repRho T)
    (modulePullback B S hS (representedSpaceMap B S hS t))
    (hF := modulePullback_additive (representedSpaceMap B S hS t))
    (modulePullbackUnitIso B S hS (representedSpaceMap B S hS t)) x

namespace BottomModel

variable {U : BigFppfOver B S hS}
  {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
    (representedAlgebraicSpace B S hS U)))} {a : ℤ} {m n : ℕ}
  {A : Matrix (Fin m) (Fin n)
    ((structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj.obj
      (op (idChart B S hS U)))}

/-- A bottom model on a represented space pulls back along `t : T ⟶ U`, with matrix `θ_t(A)`. -/
def pullbackRep (M : BottomModel K a (repRho U) A) {T : BigFppfOver B S hS} (t : T ⟶ U) :
    BottomModel ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).obj K) a
      (repRho T) (A.map (repTheta t)) :=
  M.pullback (representedSpaceMap B S hS t) (repRho T) (repTheta t) (repTheta_spec t)

/-- A bottom model with a free kernel splitting of rank `r` is universally of bottom rank `r`. -/
theorem isUniversallyFreeBottom_id_of_hasFreeKernelSplitting {Y : AlgebraicSpaces B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} {a : ℤ}
    {R : Type u} [CommRing R] {ψ : R →+* End (ringedToposUnit Y)} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) R} (M : BottomModel K a ψ A) {r : ℕ}
    (h : A.HasFreeKernelSplittingKernelRankStratum r) : IsUniversallyFreeBottom K a r (𝟙 Y) := by
  intro Y' g
  obtain ⟨e⟩ := M.nonempty_homology_iso_free h g
  exact isFiniteLocallyFreeOfIntRank_of_iso B S hS
    (e.symm ≪≫ eqToIso (congrArg (fun k => pullbackHomology K a k) (Category.comp_id g).symm))
    (isFiniteLocallyFreeOfIntRank_freeObj Y' r)

end BottomModel

/-- The map `repTheta` is contravariantly functorial: `θ_{i ≫ t} = θ_i ∘ θ_t`. -/
theorem repTheta_comp_apply {T' T U : BigFppfOver B S hS} (i : T' ⟶ T) (t : T ⟶ U)
    (x : (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj.obj
      (op (idChart B S hS U))) :
    repTheta (i ≫ t) x = repTheta i (repTheta t x) := by
  rw [repTheta_apply, repTheta_apply, repTheta_apply, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- On the open `D(s)` of an affine `T`, the function `s` becomes a unit. -/
theorem isUnit_repTheta_openSubHom (T : BigFppfOver B S hS)
    (s : (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).obj.obj
      (op (idChart B S hS T))) :
    IsUnit (repTheta (openSubHom T
      (((BigFppfOver.toScheme B S hS).obj T).basicOpen
        (show Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) from s))) s) := by
  rw [repTheta_apply]
  have hk : (BigFppfOver.toScheme B S hS).map (openSubHom T
      (((BigFppfOver.toScheme B S hS).obj T).basicOpen
        (show Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) from s))) ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).obj T).basicOpen
        (show Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) from s) = ⊤ := by
    rw [toScheme_map_openSubHom]
    exact Scheme.Opens.ι_preimage_self _
  exact RingedSpace.isUnit_of_isUnit_germ _ ⊤ _ fun z hz =>
    (RingedSpace.mem_basicOpen _ _ z hz).1
      (((Scheme.preimage_basicOpen_top _ _).symm.trans hk).ge hz)

/-- The ring of an object of the big fppf site, as the sections of the structure sheaf of the
represented space at its final chart. -/
abbrev repRing (T : BigFppfOver B S hS) : Type u :=
  (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).obj.obj
    (op (idChart B S hS T))

/-- The chart of `T` given by the open `D(s)`. -/
abbrev basicOpenChart (T : BigFppfOver B S hS) (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    SmallEtale B S hS (yoneda.obj T) :=
  openChart B S hS (yoneda.obj T) (idChart B S hS T)
    (((BigFppfOver.toScheme B S hS).obj T).basicOpen s)

/-- The chart map of `basicOpenChart T s` is the map of represented spaces induced by the
inclusion of `D(s)` into `T`. -/
theorem chartToSpace_basicOpenChart (T : BigFppfOver B S hS)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    chartToSpace B S hS (representedAlgebraicSpace B S hS T) (basicOpenChart T s) =
      representedSpaceMap B S hS (openSubHom T
        (((BigFppfOver.toScheme B S hS).obj T).basicOpen s)) :=
  InducedCategory.hom_ext (Category.comp_id _)

/-- The charts `D(s_i)` of a family generating the unit ideal cover the points of `T`. -/
theorem exists_mem_range_basicOpenChart (T : BigFppfOver B S hS) {ι : Type*}
    (s : ι → Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
    (y : points B S hS (yoneda.obj T)) :
    ∃ i, y ∈ Set.range (pointsMap B S hS (yoneda.obj (basicOpenChart T (s i)).1.left)
      (basicOpenChart T (s i)).1.hom) := by
  have hcov := iSup_basicOpen_of_span_eq_top (X := (BigFppfOver.toScheme B S hS).obj T) ⊤
    (Set.range s) hs
  have hz : pointsToScheme B S hS T y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) :=
    trivial
  rw [← hcov] at hz
  simp only [TopologicalSpace.Opens.mem_iSup, Set.mem_range, exists_prop] at hz
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hz
  exact ⟨i, (Set.ext_iff.1 (range_pointsMap_openChart (idChart B S hS T)
    (((BigFppfOver.toScheme B S hS).obj T).basicOpen (s i))) y).2
      ⟨y, hi, congrFun (pointsMap_id B S hS (yoneda.obj T)) y⟩⟩

/-- **Fitting conditions give universal local freeness.** On an affine `T`, a bottom model whose
matrix `A` has `Fit_{r-1}(C_A) = 0` and `Fit_r(C_A) = Γ(T)` makes the identity of the
represented space universally of bottom rank `r`. -/
theorem BottomModel.isUniversallyFreeBottom_of_fittingIdeal {T : BigFppfOver B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T)))} {a : ℤ} {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing T)} (M : BottomModel K a (repRho T) A)
    (h₁ : _root_.fittingIdeal (R := repRing T) (M := A.cokerTransposeKernelRankStratum)
        ((r : ℤ) - 1) = ⊥)
    (h₂ : _root_.fittingIdeal (R := repRing T)
        (M := A.cokerTransposeKernelRankStratum) (r : ℤ) = ⊤) :
    IsUniversallyFreeBottom K a r (𝟙 _) := by
  obtain ⟨ι, s, hs, hsplit⟩ := Matrix.exists_span_hasFreeKernelSplitting_kernelRankStratum A r h₁ h₂
  refine isUniversallyFreeBottom_of_forall_chart _ fun y => ?_
  obtain ⟨i, hi⟩ := exists_mem_range_basicOpenChart T
    (fun i => (s i : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))) hs y
  refine ⟨basicOpenChart T (s i), hi, ?_⟩
  let o := openSubHom T (((BigFppfOver.toScheme B S hS).obj T).basicOpen
    (s i : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))
  have e : chartToSpace B S hS (representedAlgebraicSpace B S hS T) (basicOpenChart T (s i)) ≫
      𝟙 _ = 𝟙 _ ≫ representedSpaceMap B S hS o := by
    rw [Category.comp_id, Category.id_comp]
    exact chartToSpace_basicOpenChart T _
  rw [e]
  refine (isUniversallyFreeBottom_comp_iff _ _).2
    ((M.pullbackRep o).isUniversallyFreeBottom_id_of_hasFreeKernelSplitting ?_)
  let ℓ := IsLocalization.Away.lift (S := Localization.Away (s i)) (s i)
    (isUnit_repTheta_openSubHom T (s i))
  have hℓ : ℓ.comp (algebraMap _ (Localization.Away (s i))) = repTheta o :=
    IsLocalization.Away.lift_comp _ _
  have := (hsplit i).map ℓ
  rwa [Matrix.map_map, ← RingHom.coe_comp, hℓ] at this

/-! ### Field points -/

/-- The kernel of a matrix with a free kernel splitting of rank `r` is `O^r`. -/
def kernelMatrixHomIsoFreeObj {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    [HasKernels C] (O : C) {R : Type*} [CommRing R] (ψ : R →+* End O) {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) R} (h : A.HasFreeKernelSplittingKernelRankStratum r) :
    kernel (matrixHomMatrixKernelSplitting O ψ A) ≅ freeObjMatrixKernelSplitting O r :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _)
    ((exists_isLimit_kernelFork_of_hasFreeKernelSplitting_matrixKernelSplitting
        (O := O) (ψ := ψ) h).choose_spec.choose_spec
      (𝟭 C)).some

/-- **A free kernel of rank `r` is a matrix**: if the kernel of the morphism of `A` is `O^r`, there
is an injective matrix `J` with `A J = 0`, when `ψ : R → End O` is bijective. -/
theorem exists_injective_mul_eq_zero_of_kernel_iso {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] [HasKernels C] {O : C} {R : Type*} [CommRing R] {ψ : R →+* End O}
    (hψ : Function.Bijective ψ) {m n r : ℕ} {A : Matrix (Fin m) (Fin n) R}
    (e : kernel (matrixHomMatrixKernelSplitting O ψ A) ≅ freeObjMatrixKernelSplitting O r) :
    ∃ J : Matrix (Fin n) (Fin r) R, A * J = 0 ∧ Function.Injective J.mulVec := by
  obtain ⟨J, hJ⟩ := exists_matrixHom_eq_matrixKernelSplitting hψ.2
      (e.inv ≫ kernel.ι (matrixHomMatrixKernelSplitting O ψ A))
  have : Mono (matrixHomMatrixKernelSplitting O ψ J) := by
    rw [hJ]
    infer_instance
  refine ⟨J, mul_eq_zero_of_matrixHom_comp_matrixKernelSplitting hψ.1 A J ?_,
      injective_mulVec_of_mono_matrixKernelSplitting hψ.1 J⟩
  rw [hJ, Category.assoc, kernel.condition, comp_zero]

/-- Over a field, a matrix has a free kernel splitting whose rank is the dimension of its
kernel. -/
theorem Matrix.hasFreeKernelSplitting_finrank_ker {k : Type*} [Field k] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) k) :
    A.HasFreeKernelSplittingKernelRankStratum (Module.finrank k (LinearMap.ker A.mulVecLin)) :=
  Matrix.hasFreeKernelSplitting_of_basis_kernelRankStratum A
    (Module.finBasisOfFinrankEq k _ (Matrix.finrank_cokerTranspose_kernelRankStratum A))

/-- **The rank of a free module is determined by its local rank** on a nonempty algebraic
space. -/
theorem natCast_eq_of_isFiniteLocallyFreeOfIntRank_freeObj {Y : AlgebraicSpaces B S hS}
    (y : points B S hS Y.1) {d : ℕ} {r : ℤ}
    (h : SheafOfModules.IsFiniteLocallyFreeOfIntRank
        (freeObjMatrixKernelSplitting (ringedToposUnit Y) d) r) :
    (d : ℤ) = r := by
  obtain ⟨V, ⟨v, -⟩, n, rfl, ⟨e⟩⟩ :=
    (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS _ r).1 h y
  let TV := (SmallEtale.toOver B S hS Y.1).obj V
  let e' : freeObjMatrixKernelSplitting (ringedToposUnit (representedAlgebraicSpace B S hS TV)) d ≅
      freeObjMatrixKernelSplitting (ringedToposUnit (representedAlgebraicSpace B S hS TV)) n :=
    (freeObjMapIsoMatrixKernelSplitting (pb (chartToSpace B S hS Y V))
        (pbUnitIso (chartToSpace B S hS Y V)) d).symm ≪≫
      e ≪≫ Stacks.SheafOfModules.freeULiftFinIsoBiproduct
        (structureSheaf B S hS (yoneda.obj TV) (isAlgebraicSpace_yoneda B S hS TV)) n
  let G := homModule (ringedToposUnit (representedAlgebraicSpace B S hS TV)) (repRho TV)
  let L : (Fin d → repRing TV) ≃ₗ[repRing TV] (Fin n → repRing TV) :=
    (homModuleFiniteFreeEquiv (bijective_repRho TV) d).symm ≪≫ₗ (G.mapIso e').toLinearEquiv ≪≫ₗ
      homModuleFiniteFreeEquiv (bijective_repRho TV) n
  have : Nontrivial (repRing TV) := by
    let X := (BigFppfOver.toScheme B S hS).obj TV
    let x : X := pointsToScheme B S hS TV v
    exact RingHom.domain_nontrivial (X.presheaf.germ ⊤ x trivial).hom
  simpa only [Module.finrank_fin_fun, Nat.cast_inj] using L.finrank_eq

/-- A field point of `T` whose scheme point lies in the zero locus of an ideal kills it. -/
theorem repTheta_eq_zero_of_schemePoint_mem_zeroLocus {T : BigFppfOver B S hS}
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (p : FieldValuedPoint B S hS (yoneda.obj T))
    (hx : schemePoint B S hS T p ∈ ((BigFppfOver.toScheme B S hS).obj T).zeroLocus (U := ⊤)
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))
    (f : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hf : f ∈ I) : repTheta p.value f = 0 := by
  let X := (BigFppfOver.toScheme B S hS).obj T
  by_contra hne
  obtain ⟨g, hg⟩ := (isField_structureSheaf_idChart B S hS p).mul_inv_cancel hne
  have hu : IsUnit (((BigFppfOver.toScheme B S hS).map p.value).appTop f) := by
    rw [← repTheta_apply p.value f]
    exact .of_mul_eq_one g hg
  have hmem : IsLocalRing.closedPoint p.carrier ∈
      (BigFppfOver.toScheme B S hS).map p.value ⁻¹ᵁ X.basicOpen (show Γ(X, ⊤) from f) := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact (X.mem_zeroLocus_iff _ _).1 hx f hf hmem

/-- Above a proper ideal of the ring of an affine object of the site there is a geometric point
whose ring map kills it. -/
theorem exists_geometricPoint_repTheta_eq_zero (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (I : Ideal (repRing T)) (hI : I ≠ ⊤) :
    ∃ p : GeometricPoint B S hS (yoneda.obj T), ∀ f ∈ I, repTheta p.val.value f = 0 := by
  let X := (BigFppfOver.toScheme B S hS).obj T
  let J : Ideal Γ(X, ⊤) := I
  let I' : Set Γ(X, ⊤) := (J : Set Γ(X, ⊤))
  obtain ⟨q, hq⟩ : (PrimeSpectrum.zeroLocus I').Nonempty := by
    rwa [Set.nonempty_iff_ne_empty, Ne, PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have hx : X.isoSpec.inv q ∈ X.zeroLocus (U := ⊤) I' := by
    rw [← X.isoSpec_inv_image_zeroLocus]
    exact ⟨q, hq, rfl⟩
  obtain ⟨p₀, hp₀⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS T (X.isoSpec.inv q)
  obtain ⟨p, hp⟩ := (geometricPoints_large_enough B S hS _ _ (isAlgebraicSpace_yoneda B S hS T)
    (isAlgebraicSpace_yoneda B S hS T)).1 (p₀.class B S hS _)
  have hs : schemePoint B S hS T p.val = X.isoSpec.inv q := by
    rw [← hp₀, ← pointsToScheme_class, ← pointsToScheme_class]
    exact congrArg _ hp
  exact ⟨p, repTheta_eq_zero_of_schemePoint_mem_zeroLocus J p.val (hs ▸ hx)⟩

/-- Above a proper ideal of the ring of an affine object of the site there is a field point
whose ring map kills it. -/
theorem exists_fieldValuedPoint_repTheta_eq_zero (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (I : Ideal (repRing T)) (hI : I ≠ ⊤) :
    ∃ p : FieldValuedPoint B S hS (yoneda.obj T), ∀ f ∈ I, repTheta p.value f = 0 :=
  let ⟨p, hp⟩ := exists_geometricPoint_repTheta_eq_zero T I hI
  ⟨p.val, hp⟩

/-- **Universal local freeness at field points forces `Fit_r(C_A)` to be the unit ideal.** For a
bottom model on an affine `T` with matrix `A`, if `H^a` of the pullback of `K` to every field
point of `T` is locally free of rank `r`, then `Fit_r(C_A) = Γ(T)`: at a field point `k` the
kernel of `A ⊗ k` is free of rank `dim ker (A ⊗ k)`, which is then `r`. -/
theorem BottomModel.fittingIdeal_eq_top_of_forall_fieldValuedPoint {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T)))} {a : ℤ} {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing T)} (M : BottomModel K a (repRho T) A)
    (h : ∀ p : FieldValuedPoint B S hS (yoneda.obj T),
      SheafOfModules.IsFiniteLocallyFreeOfIntRank
        (pullbackHomology K a (representedSpaceMap B S hS p.value)) (r : ℤ)) :
    _root_.fittingIdeal (R := repRing T) (M := A.cokerTransposeKernelRankStratum) (r : ℤ) = ⊤ := by
  by_contra hne
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_repTheta_eq_zero T _ hne
  let ε : repRing p.siteObject ≃+* p.carrier :=
    (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).commRingCatIsoToRingEquiv
  let φ : repRing T →+* p.carrier := ε.toRingHom.comp (repTheta p.value)
  refine Matrix.not_fittingIdeal_cokerTranspose_le_kernelRankStratum A φ r ?_
    (fun f hf => (RingHom.mem_ker).2 (by simp [φ, hp f hf]))
  have hsplit := (Matrix.hasFreeKernelSplitting_finrank_ker (A.map φ)).map ε.symm.toRingHom
  have hφ : (A.map φ).map ε.symm.toRingHom = A.map (repTheta p.value) := by
    ext i j
    simp only [Matrix.map_apply, φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  rw [hφ] at hsplit
  have hfree := isFiniteLocallyFreeOfIntRank_of_iso B S hS
    ((M.pullbackRep p.value).homologyIsoKernel ≪≫ kernelMatrixHomIsoFreeObj _ _ hsplit) (h p)
  have := natCast_eq_of_isFiniteLocallyFreeOfIntRank_freeObj
    ((p.tautologicalPoint B S hS).class B S hS _) hfree
  omega

/-! ### The kernel test on charts -/

/-- The morphism to `T` of a chart of the represented space of `T`. -/
abbrev chartMapToRep {T : BigFppfOver B S hS} (V : SmallEtale B S hS (yoneda.obj T)) :
    V.1.left ⟶ T :=
  (SmallEtale.toOver B S hS (yoneda.obj T)).map ((isTerminal_idChart B S hS T).from V)

/-- The chart map of a chart `V` of the represented space of `T` is the map of represented
spaces induced by `chartMapToRep V`. -/
theorem chartToSpace_eq_representedSpaceMap {T : BigFppfOver B S hS}
    (V : SmallEtale B S hS (yoneda.obj T)) :
    chartToSpace B S hS (representedAlgebraicSpace B S hS T) V =
      representedSpaceMap B S hS (chartMapToRep V) :=
  InducedCategory.hom_ext ((CostructuredArrow.w ((isTerminal_idChart B S hS T).from V).1).symm.trans
    (Category.comp_id _))

/-- **A function on `T` vanishing on étale charts through every point is zero.** -/
theorem eq_zero_of_forall_chart {T : BigFppfOver B S hS}
    (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (h : ∀ y : points B S hS (yoneda.obj T), ∃ V : SmallEtale B S hS (yoneda.obj T),
      y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
        ((BigFppfOver.toScheme B S hS).map (chartMapToRep V)).appTop x = 0) : x = 0 := by
  choose V hV hx using h
  have hcov : (SmallEtale.topology B S hS (yoneda.obj T)).CoversTop V :=
    SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hV y⟩
  have hsh := isSheaf_globalSections B S hS (yoneda.obj T)
  refine (hsh.isSeparated _ (hcov (idChart B S hS T))).ext fun W f hf => ?_
  obtain ⟨i, ⟨b⟩⟩ := hf
  obtain rfl : f = b ≫ (isTerminal_idChart B S hS T).from (V i) :=
    (isTerminal_idChart B S hS T).hom_ext _ _
  change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj T)).map
      (b ≫ (isTerminal_idChart B S hS T).from (V i)))).appTop x =
    ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj T)).map
      (b ≫ (isTerminal_idChart B S hS T).from (V i)))).appTop 0
  rw [map_zero, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop]
  exact (congrArg (((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS (yoneda.obj T)).map b)).appTop) (hx i)).trans (map_zero _)

/-- If `Fit_r(C_A)` is the unit ideal, so is `Fit_r(C_{θ_t(A)})` for any `t : T ⟶ U`. -/
private theorem fittingIdeal_map_repTheta_eq_top {T U : BigFppfOver B S hS} (t : T ⟶ U)
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) (repRing U)} {r : ℤ}
    (h : _root_.fittingIdeal (R := repRing U) (M := A.cokerTransposeKernelRankStratum) r = ⊤) :
    _root_.fittingIdeal (R := repRing T)
      (M := (A.map (repTheta t)).cokerTransposeKernelRankStratum) r = ⊤ := by
  rw [Matrix.fittingIdeal_cokerTranspose_map_kernelRankStratum, h, Ideal.map_top]

/-- **The kernel test.** For a bottom model on `T` with matrix `A` such that `Fit_r(C_A) = Γ(T)`,
if `H^a(K)` is finite locally free of rank `r` then `Fit_{r-1}(C_A) = 0`: on an étale chart where
`H^a(K) ≅ 𝒪^r` the kernel of `A` contains an injective `J : 𝒪^r → 𝒪^n` with `A J = 0`. -/
theorem BottomModel.fittingIdeal_pred_eq_bot {T : BigFppfOver B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T)))} {a : ℤ} {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing T)} (M : BottomModel K a (repRho T) A)
    (h₂ : _root_.fittingIdeal (R := repRing T) (M := A.cokerTransposeKernelRankStratum) (r : ℤ) = ⊤)
    (hK : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((DerivedCategory.homologyFunctor _ a).obj K) (r : ℤ)) :
    _root_.fittingIdeal (R := repRing T) (M := A.cokerTransposeKernelRankStratum)
        ((r : ℤ) - 1) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx =>
    eq_zero_of_forall_chart (T := T) (show Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) from x)
      fun y => ?_
  obtain ⟨V, hV, n', hn', ⟨e⟩⟩ :=
    (isFiniteLocallyFreeOfIntRank_iff_forall_chart B S hS _ r).1 hK y
  obtain rfl : n' = r := by omega
  refine ⟨V, hV, ?_⟩
  let v := chartMapToRep V
  let Av := A.map (repTheta v)
  let O := ringedToposUnit (representedAlgebraicSpace B S hS V.1.left)
  let eK : kernel (matrixHomMatrixKernelSplitting O (repRho V.1.left) Av) ≅
      freeObjMatrixKernelSplitting O n' :=
    (M.pullbackRep v).homologyIsoKernel.symm ≪≫
      (DerivedCategory.homologyFunctor _ a).mapIso (eqToIso (congrArg
        (fun g => (smallEtaleDerivedModulePullback B S hS g).obj K)
        (chartToSpace_eq_representedSpaceMap V).symm)) ≪≫
      smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale _ (isEtale_chartToSpace B S hS _ V) K a ≪≫
      e ≪≫ Stacks.SheafOfModules.freeULiftFinIsoBiproduct
        (structureSheaf B S hS (yoneda.obj V.1.left) (isAlgebraicSpace_yoneda B S hS _)) n'
  obtain ⟨J, hAJ, hinj⟩ := exists_injective_mul_eq_zero_of_kernel_iso (bijective_repRho V.1.left) eK
  have hbot := Matrix.fittingIdeal_cokerTranspose_pred_eq_bot_kernelRankStratum Av
    (fittingIdeal_map_repTheta_eq_top v h₂) J hAJ hinj
  rw [Matrix.fittingIdeal_cokerTranspose_map_kernelRankStratum] at hbot
  have hx0 : repTheta v x = 0 := by
    have := Ideal.mem_map_of_mem (repTheta v) hx
    rwa [hbot, Ideal.mem_bot] at this
  exact (repTheta_apply v x).symm.trans hx0

/-- The pullback homology along a composite is the pullback homology of the derived pullback. -/
def pullbackHomologyCompIso {X Y Y' : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    (f : Y ⟶ X) (g : Y' ⟶ Y) :
    pullbackHomology ((smallEtaleDerivedModulePullback B S hS f).obj E) a g ≅
      pullbackHomology E a (g ≫ f) :=
  (DerivedCategory.homologyFunctor _ a).mapIso
    ((smallEtaleDerivedModulePullbackCompIso B S hS g f).app E)

/-- **Stacks 0BDL on a chart with a bottom model.** For a bottom model of `K` on the represented
space of `U` with matrix `A`, and `t : T ⟶ U` with `T` affine, the morphism `t` is universally of
bottom rank `r` for `K` exactly when `Fit_{r-1}(C_A)` maps to zero and `Fit_r(C_A)` to the unit
ideal of `Γ(T)` under `θ_t`. -/
theorem BottomModel.isUniversallyFreeBottom_iff {U : BigFppfOver B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS U)))} {a : ℤ} {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing U)} (M : BottomModel K a (repRho U) A)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : T ⟶ U) :
    IsUniversallyFreeBottom K a r (representedSpaceMap B S hS t) ↔
      _root_.fittingIdeal (R := repRing T)
          (M := (A.map (repTheta t)).cokerTransposeKernelRankStratum)
          ((r : ℤ) - 1) = ⊥ ∧
        _root_.fittingIdeal (R := repRing T)
            (M := (A.map (repTheta t)).cokerTransposeKernelRankStratum)
          (r : ℤ) = ⊤ := by
  let M' := M.pullbackRep t
  constructor
  · intro h
    have htop := M'.fittingIdeal_eq_top_of_forall_fieldValuedPoint fun p =>
      isFiniteLocallyFreeOfIntRank_of_iso B S hS (pullbackHomologyCompIso K a _ _).symm
        (h _ (representedSpaceMap B S hS p.value))
    refine ⟨M'.fittingIdeal_pred_eq_bot htop ?_, htop⟩
    have := h _ (𝟙 _)
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    simpa only [Category.id_comp] using (isUniversallyFreeBottom_comp_iff (E := K) (a := a)
      (r := r) (representedSpaceMap B S hS t) (𝟙 _)).2
        (M'.isUniversallyFreeBottom_of_fittingIdeal h₁ h₂)

/-- **Where `Fit_r(C_A)` is the unit ideal, plain local freeness of `H^a` is universal.** -/
theorem BottomModel.isUniversallyFreeBottom_of_fittingIdeal_eq_top {U : BigFppfOver B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS U)))} {a : ℤ} {m n r : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing U)} (M : BottomModel K a (repRho U) A)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : T ⟶ U)
    (htop : _root_.fittingIdeal (R := repRing U)
        (M := A.cokerTransposeKernelRankStratum) (r : ℤ) = ⊤)
    (hK : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      (pullbackHomology K a (representedSpaceMap B S hS t)) (r : ℤ)) :
    IsUniversallyFreeBottom K a r (representedSpaceMap B S hS t) := by
  have htop' := fittingIdeal_map_repTheta_eq_top t htop
  exact (M.isUniversallyFreeBottom_iff t).2
    ⟨(M.pullbackRep t).fittingIdeal_pred_eq_bot htop' hK, htop'⟩

/-- The dimension over `Γ(T)` of the global sections of a module on the represented space of
`T`. -/
def sectionsFinrank (T : BigFppfOver B S hS)
    (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T))) : ℕ :=
  Module.finrank (repRing T)
    ((homModule (ringedToposUnit (representedAlgebraicSpace B S hS T)) (repRho T)).obj N)

/-- Isomorphic modules have global sections of the same dimension. -/
theorem sectionsFinrank_eq_of_iso {T : BigFppfOver B S hS}
    {N N' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T))} (e : N ≅ N') :
    sectionsFinrank T N = sectionsFinrank T N' :=
  ((homModule _ (repRho T)).mapIso e).toLinearEquiv.finrank_eq

/-- The dimension of the global sections of a module isomorphic to `H^a` of the pullback of a
bottom model along `t`, when the pulled-back matrix has a free kernel splitting of rank `d`. -/
theorem BottomModel.sectionsFinrank_of_iso {U : BigFppfOver B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS U)))} {a : ℤ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing U)} (M : BottomModel K a (repRho U) A)
    {T : BigFppfOver B S hS} [Nontrivial (repRing T)] (t : T ⟶ U) {d : ℕ}
    (h : (A.map (repTheta t)).HasFreeKernelSplittingKernelRankStratum d)
    {N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T))}
    (e : N ≅ pullbackHomology K a (representedSpaceMap B S hS t)) :
    sectionsFinrank T N = d := by
  rw [sectionsFinrank_eq_of_iso (e ≪≫ (M.pullbackRep t).homologyIsoKernel ≪≫
    kernelMatrixHomIsoFreeObj _ _ h), sectionsFinrank,
    (homModuleFiniteFreeEquiv (bijective_repRho T) _).finrank_eq, Module.finrank_fin_fun]

/-- A bound on the dimension of the global sections of a module holds for every isomorphic
module. -/
theorem sectionsFinrank_le_of_iso {T : BigFppfOver B S hS}
    {N N' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T))} (e : N ≅ N') {r : ℕ}
    (h : sectionsFinrank T N ≤ r) : sectionsFinrank T N' ≤ r :=
  (sectionsFinrank_eq_of_iso e) ▸ h

/-- A bound on the dimension of the global sections of `H^a` of the pullback of a bottom model
bounds the rank of a free kernel splitting of the pulled-back matrix. -/
theorem BottomModel.le_of_sectionsFinrank_le {U : BigFppfOver B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS U)))} {a : ℤ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing U)} (M : BottomModel K a (repRho U) A)
    {T : BigFppfOver B S hS} [Nontrivial (repRing T)] (t : T ⟶ U) {d r : ℕ}
    (h : (A.map (repTheta t)).HasFreeKernelSplittingKernelRankStratum d)
    (hr : sectionsFinrank T (pullbackHomology K a (representedSpaceMap B S hS t)) ≤ r) : d ≤ r :=
  (M.sectionsFinrank_of_iso t h (Iso.refl _)) ▸ hr

/-- A bound on the dimension of the global sections of a module isomorphic to `H^a` of the
pullback of a bottom model bounds the rank of a free kernel splitting of the pulled-back
matrix. -/
theorem BottomModel.le_of_sectionsFinrank_le_of_iso {U : BigFppfOver B S hS}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS U)))} {a : ℤ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) (repRing U)} (M : BottomModel K a (repRho U) A)
    {T : BigFppfOver B S hS} [Nontrivial (repRing T)] (t : T ⟶ U) {d r : ℕ}
    (h : (A.map (repTheta t)).HasFreeKernelSplittingKernelRankStratum d)
    {N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedAlgebraicSpace B S hS T))}
    (e : N ≅ pullbackHomology K a (representedSpaceMap B S hS t))
    (hr : sectionsFinrank T N ≤ r) : d ≤ r :=
  (M.sectionsFinrank_of_iso t h e) ▸ hr

end AlgebraicGeometry.Space
