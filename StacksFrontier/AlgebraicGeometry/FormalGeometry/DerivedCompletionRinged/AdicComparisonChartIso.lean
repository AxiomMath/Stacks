module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimitCoprojections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientComparisonPinned
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ClosureProductsAndFibres
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionUnitIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedHomHomotopyColimitProjections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicDualDegreeZero
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedSheafHomFactorisation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalCalculationFiniteType
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Exactness
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitEventualFactorisation
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjectionsFunctor

/-!
# The comparison of part (1) of [Stacks, Tag 0A0K] is invertible on a chart

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` generating the sheaf
of ideals `ℐ`, and let `K ∈ D(𝒪)`. The Čech completion `K^∧` is a derived limit of the adic
reduction tower `T : n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` through the canonical factorizations of
[Stacks, Tag 0CQH], as soon as the Koszul cohomology sheaves are pro-zero below the top degree
(`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_adicReductionTower_completion`).
This file proves that **every** other derived-limit presentation `L` of `T`, compared with `K^∧`
through a map `c` matching the two families of projections, is isomorphic to it through `c`.

That is not formal. A map between two derived limits of one tower which matches their projections
need not be invertible: it is determined only up to a map factoring through `(∏ₙ Tₙ)⟦-1⟧`, the
phantom indeterminacy of the Milnor sequence of [Stacks, Tag 0919]. It is this indeterminacy,
not a missing presentation, that stands between the chart-level form of part (1) and part (1)
at the source's hypotheses, whose globalization needs a *named* comparison map.

## The argument

Both ends of `c` are derived complete along `ℐ`, so `c` is invertible as soon as each
`R𝑆heafHom_𝒪(K^k, c)` is, `K^k` running over the Koszul complexes on the powers of the `f_i`:
the cone of `c` is derived complete, and a derived-complete object `E` with
`R𝑆heafHom_𝒪(K^k, E) = 0` for every `k` is zero, being the derived limit of these by
[Stacks, Tag 0A0E] (`isZero_of_forall_isZero_derivedSheafHom_koszulPowerComplex`).

After `G_k = R𝑆heafHom_𝒪(K^k, -)` the indeterminacy dies: every transition map of the tower
`G_k ∘ T` factors, from a later level on, through the constant object `G_k(K)` compatibly with
the derived reductions, and for such a tower a map into a derived limit is determined by its
projections (`NoetherianAdicCompletion.isIso_of_comp_proj_of_exists_factor`). The factorization
is the Koszul-index computation
`AlgebraicGeometry.RingedSite.exists_factor_derivedSheafHomSystem_koszulPowerSystem` — on the
tower `n ↦ R𝑆heafHom_𝒪(K^n, K)` of
[Stacks, Tag 0A0E], multiplication by `f_i^{k+1}` being null-homotopic on `K^k` — transported to
the adic tower along the Artin–Rees comparison `ψ` of [Stacks, Tag 0921], which has eventual
inverses under the pro-vanishing hypothesis.

## Main results

* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.map_of_exists_distinguished` lives in
  `Homology/DerivedCategory/InverseSystem/DerivedLimitWithProjectionsFunctor.lean`; it is what
  carries a presentation along `G_k`, which is not known to be a triangulated functor here.
* `AlgebraicGeometry.RingedSite.isZero_of_forall_isZero_derivedSheafHom_koszulPowerComplex` —
  derived Nakayama in Koszul form.
* `AlgebraicGeometry.RingedSite.isIso_of_forall_isIso_derivedSheafHom_koszulPowerComplex_map` —
  a map between derived-complete objects inverted by every `G_k` is invertible.
* `AlgebraicGeometry.RingedSite.isIso_of_comp_proj_completionFunctor_of_exists_factor` — the
  comparison on a chart is invertible.

## References

* [Stacks Project, Tag 0919](https://stacks.math.columbia.edu/tag/0919)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

open MonoidalCategory
open scoped IsMulCommutative

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules hasSheafCompose_forget₂_ringCat
  isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf

section Detection

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance]
  RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf_adicQuotientFactorization

/-- **Derived Nakayama in Koszul form.** An object of `D(𝒪)` derived complete along the ideal sheaf
generated by `f_1, …, f_r` vanishes as soon as `R𝑆heafHom_𝒪(K^k, -)` kills it for every Koszul
complex `K^k` on the powers of the `f_i`: by [Stacks, Tag 0A0E] its completion is a derived limit
of these, hence zero, and it is its own completion. -/
theorem isZero_of_forall_isZero_derivedSheafHom_koszulPowerComplex
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    {E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hE : IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f) E)
    (h : ∀ k : ℕ, IsZero (((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj (koszulPowerComplex X f k)))).obj E)) :
    IsZero E := by
  obtain ⟨c, hc⟩ := exists_isHomotopyColimitWithCoprojections_koszulPowerSystem X f
  obtain ⟨δ, hT⟩ := isDerivedLimitWithProjections_derivedSheafHom_of_coprojections X
    (koszulPowerSystem X f ⋙ DerivedCategory.Q) E
    (isIso_derivedSheafHomSigmaComparison X _ E) hc
  have hprod : IsZero (∏ᶜ fun n : ℕ ↦
      (derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) E).obj (op n)) := by
    rw [IsZero.iff_id_eq_zero]
    exact Pi.hom_ext _ _ fun n ↦ (h n).eq_of_tgt _ _
  have hcomp : IsZero ((completionFunctor X f).obj E) :=
    Triangle.isZero₁_of_isZero₂₃ _ hT hprod hprod
  rw [generatedIdealSheaf_eq_idealOfGlobalSections] at hE
  have := isIso_completionUnit_app_of_isDerivedComplete_idealOfGlobalSections X f E hE
  exact hcomp.of_iso (asIso ((completionUnit X f).app E))

/-- **A map between derived-complete objects inverted by every `R𝑆heafHom_𝒪(K^k, -)` is
invertible.** Its cone is derived complete, the derived-complete objects forming a triangulated
subcategory, and is killed by every `R𝑆heafHom_𝒪(K^k, -)`, which is exact by
[Stacks, Tag 08JC]; so it vanishes by
`AlgebraicGeometry.RingedSite.isZero_of_forall_isZero_derivedSheafHom_koszulPowerComplex`. -/
theorem isIso_of_forall_isIso_derivedSheafHom_koszulPowerComplex_map
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hA : IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f) A)
    (hB : IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f) B) (c : A ⟶ B)
    (h : ∀ k : ℕ, IsIso (((derivedSheafHomBifunctor X).obj
      (op (DerivedCategory.Q.obj (koszulPowerComplex X f k)))).map c)) :
    IsIso c := by
  obtain ⟨E, g, δ, hT⟩ := distinguished_cocone_triangle c
  have hE₁ : IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f) (E⟦(-1 : ℤ)⟧) :=
    isDerivedComplete_of_distTriang X _ (inv_rot_of_distTriang _ hT) hA hB
  have hE : IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f) E :=
    ObjectProperty.prop_of_iso (IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f))
      ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by norm_num)).app E)
      (isDerivedComplete_shiftFunctor_obj X _ (1 : ℤ) hE₁)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
  refine isZero_of_forall_isZero_derivedSheafHom_koszulPowerComplex X f hE fun k ↦ ?_
  obtain ⟨δ', hT'⟩ := exists_distinguished_derivedSheafHom_second X
    (DerivedCategory.Q.obj (koszulPowerComplex X f k)) _ hT
  exact (Triangle.isZero₃_iff_isIso₁ _ hT').2 (by simpa using h k)

end Detection

section Chart

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance]
  RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf_adicQuotientFactorization

/-- **The comparison of part (1) of [Stacks, Tag 0A0K] is invertible on a chart.** Let `L` be any
derived limit of the adic reduction tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`, `ℐ` generated by the global
sections `f_1, …, f_r`, through projections `π`, and let `c : K^∧ ⟶ L` out of the Čech completion
match the projections `π` with the canonical factorizations of [Stacks, Tag 0CQH]. Then `c` is an
isomorphism, granted the pro-vanishing `hpz` of the Koszul cohomology sheaves below the top
degree.

See the module documentation for why matching projections is not enough by itself, and how the
detecting functors `R𝑆heafHom_𝒪(K^k, -)` remove the indeterminacy. -/
theorem isIso_of_comp_proj_completionFunctor_of_exists_factor
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {π : ∀ n : ℕ, L ⟶ (adicReductionTower X (generatedIdealSheaf f) K).obj ⟨n⟩}
    (hL : NoetherianAdicCompletion.IsDerivedLimitWithProjections
      (adicReductionTower X (generatedIdealSheaf f) K) L π)
    (c : (completionFunctor X f).obj K ⟶ L)
    (hc : ∀ n : ℕ, c ≫ π n = (reflectorIsoCompletionFunctor X f K).inv ≫
      derivedCompletionAdicFactor X (generatedIdealSheaf f) K (n + 1)) :
    IsIso c := by
  set T := adicReductionTower X (generatedIdealSheaf f) K
  refine isIso_of_forall_isIso_derivedSheafHom_koszulPowerComplex_map X f
    (isDerivedComplete_generatedIdealSheaf_completionFunctor_obj X f K)
    (isDerivedComplete_of_isDerivedLimit X _ T L hL.isDerivedLimit
      fun n ↦ isDerivedComplete_derivedTensor_adicQuotient X _ K (n + 1)) c fun k ↦ ?_
  set B := DerivedCategory.Q.obj (koszulPowerComplex X f k)
  set G := (derivedSheafHomBifunctor X).obj (op B)
  have : PreservesLimitsOfSize.{0, 0} G :=
    (derivedTensorHomAdjunction X B).rightAdjoint_preservesLimits
  have hG := fun (T' : Triangle _) (hT' : T' ∈ distTriang _) ↦
    exists_distinguished_derivedSheafHom_second X B T' hT'
  -- the constant cone `G(K) ⟶ G(Tₙ)` of the derived reductions
  let φ : ∀ n : ℕ, G.obj K ⟶ (T ⋙ G).obj ⟨n⟩ := fun n ↦
    G.map (adicQuotientReduction X (generatedIdealSheaf f) K (n + 1))
  have hφ : ∀ {m n : ℕ} (h : n ≤ m), φ m ≫ (T ⋙ G).map (homOfLE h).op = φ n := by
    intro m n h
    show G.map _ ≫ G.map (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).map
        ((adicQuotientTower X (generatedIdealSheaf f)).map (homOfLE h).op))) = _
    rw [adicQuotientTower_map_eq X f h]
    exact (G.map_comp _ _).symm.trans
      (congrArg G.map (adicQuotientReduction_comp_map X _ K (Nat.succ_le_succ h)))
  -- the factorization, transported from the Koszul tower along `ψ`
  let F₀ := derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q) K ⋙ G
  let φ₀ : ∀ n : ℕ, G.obj K ⟶ F₀.obj ⟨n⟩ := fun n ↦
    G.map ((derivedStructureSheafHomIso X K).inv ≫
      ((derivedSheafHomBifunctor X).map
        (DerivedCategory.Q.map (koszulCechComplexMap X f n ≫ cechAugmentation X f)).op).app K)
  have hfac₀ : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (t : F₀.obj ⟨m⟩ ⟶ G.obj K),
      t ≫ φ₀ n = F₀.map (homOfLE h).op := by
    intro n
    obtain ⟨m, h, t, ht⟩ := exists_factor_derivedSheafHomSystem_koszulPowerSystem X f K k n
    refine ⟨m, h, t ≫ G.map (derivedStructureSheafHomIso X K).hom, ?_⟩
    refine Eq.trans ?_ ht
    rw [Category.assoc]
    congr 1
    exact (G.map_comp _ _).symm.trans (congrArg G.map (Iso.hom_inv_id_assoc _ _))
  let ψ₁ := Functor.whiskerRight (koszulTensorDualSystemIso X f K).inv G
  let ψ₂ := Functor.whiskerRight (Functor.whiskerRight (derivedSheafHomToAdicQuotientTower X f)
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj K)) G
  have hψ₂ : NoetherianAdicCompletion.HasEventualInverses ψ₂ :=
    ((hasEventualInverses_derivedSheafHomToAdicQuotientTower X f hpz).whiskerRight _).whiskerRight _
  have hfac₂ := NoetherianAdicCompletion.exists_factor_of_comp_of_hasEventualInverses hψ₂
    (NoetherianAdicCompletion.exists_factor_of_comp_of_hasEventualInverses
      (NoetherianAdicCompletion.hasEventualInverses_of_isIso ψ₁) hfac₀)
  have hφeq : ∀ n : ℕ, (φ₀ n ≫ ψ₁.app ⟨n⟩) ≫ ψ₂.app ⟨n⟩ = φ n := fun n ↦ by
    have e := eq_adicQuotientReduction_of_dual_comp_eq X (generatedIdealSheaf f) f K n (n + 1)
      (DerivedCategory.Q.map (koszulCechComplexMap X f n ≫ cechAugmentation X f))
      ((derivedSheafHomToAdicQuotientTower X f).app (op n))
      (derivedStructureSheafHomIso_inv_comp_map_comp_derivedSheafHomToAdicQuotientTower X f n)
    refine Eq.trans ?_ (congrArg G.map e)
    refine (congrArg (· ≫ _) (G.map_comp _ _).symm).trans ((G.map_comp _ _).symm.trans
      (congrArg G.map ?_))
    exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
      ((congrArg (fun x ↦ (derivedStructureSheafHomIso X K).inv ≫ x)
        (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm))
  have hfac : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (t : (T ⋙ G).obj ⟨m⟩ ⟶ G.obj K),
      t ≫ φ n = (T ⋙ G).map (homOfLE h).op := fun n ↦ by
    obtain ⟨m, h, t, ht⟩ := hfac₂ n
    exact ⟨m, h, t, hφeq n ▸ ht⟩
  exact NoetherianAdicCompletion.isIso_of_comp_proj_of_exists_factor (T ⋙ G) φ hφ hfac
    ((isDerivedLimitWithProjections_adicReductionTower_completion X f K hpz)
      |>.map_of_exists_distinguished G hG) (hL.map_of_exists_distinguished G hG)
    (G.map c) fun n ↦ (G.map_comp _ _).symm.trans (congrArg G.map (hc n))

/-- **The chart comparison at the reflector, at any ideal equal to the generated one.** The same
statement as `AlgebraicGeometry.RingedSite.isIso_of_comp_proj_completionFunctor_of_exists_factor`
with the derived completion `K^∧` of [Stacks, Tag 099F] in place of the Čech completion and the
canonical factorizations of [Stacks, Tag 0CQH] themselves as its projections, stated at a sheaf
of ideals `J` given only to be *equal* to the one generated by the `f_i` — which is the form in
which a slice of a scheme over an affine open supplies its generators. -/
theorem isIso_of_comp_proj_derivedCompletionAdicFactor_of_exists_factor
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (J : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X J)).IsRightAdjoint]
    (hJ : J = generatedIdealSheaf f)
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {π : ∀ n : ℕ, L ⟶ (adicReductionTower X J K).obj ⟨n⟩}
    (hL : NoetherianAdicCompletion.IsDerivedLimitWithProjections (adicReductionTower X J K) L π)
    (c : (derivedCompletion X J).obj K ⟶ L)
    (hc : ∀ n : ℕ, c ≫ π n = derivedCompletionAdicFactor X J K (n + 1)) :
    IsIso c := by
  subst hJ
  have := isIso_of_comp_proj_completionFunctor_of_exists_factor X f hpz K hL
    ((reflectorIsoCompletionFunctor X f K).inv ≫ c) fun n ↦
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (hc n))
  rw [← Iso.hom_inv_id_assoc (reflectorIsoCompletionFunctor X f K) c]
  infer_instance

/-- **The pinned comparison of part (1) of [Stacks, Tag 0A0K] is invertible on a chart.** Let `L`
be a derived limit of the adic reduction tower through projections `π`, and `u : K ⟶ L` a map
whose composites with the projections are the derived reductions of [Stacks, Tag 0CQH]. Then the
map `K^∧ ⟶ L` the universal property of the derived completion attaches to `u`
(`AlgebraicGeometry.RingedSite.pinnedAdicComparison`) is an isomorphism, on any ringed site where
the ideal is generated by global sections whose Koszul cohomology sheaves are pro-zero below the
top degree.

Its composites with the projections are the canonical factorizations, both restricting along the
completion unit to the derived reductions; so this is
`AlgebraicGeometry.RingedSite.isIso_of_comp_proj_derivedCompletionAdicFactor_of_exists_factor`. -/
theorem isIso_pinnedAdicComparison_of_exists_factor
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (J : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X J)).IsRightAdjoint]
    (hJ : J = generatedIdealSheaf f)
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hLc : IsDerivedComplete.{u, u, u, u} X J L) (u : K ⟶ L)
    {π : ∀ n : ℕ, L ⟶ (adicReductionTower X J K).obj ⟨n⟩}
    (hL : NoetherianAdicCompletion.IsDerivedLimitWithProjections (adicReductionTower X J K) L π)
    (hu : ∀ n : ℕ, u ≫ π n = adicQuotientReduction X J K (n + 1)) :
    IsIso (pinnedAdicComparison X J hLc u) :=
  isIso_of_comp_proj_derivedCompletionAdicFactor_of_exists_factor X f hpz K J hJ hL _
    fun n ↦ derivedCompletion_hom_ext X J
      (isDerivedComplete_derivedTensor_adicQuotient X J K (n + 1))
      ((derivedCompletionUnit_comp_pinnedAdicComparison_assoc X J hLc u (π n)).trans
        ((hu n).trans (derivedCompletionUnit_comp_derivedCompletionAdicFactor X J K (n + 1)).symm))

end Chart

end AlgebraicGeometry.RingedSite

end
