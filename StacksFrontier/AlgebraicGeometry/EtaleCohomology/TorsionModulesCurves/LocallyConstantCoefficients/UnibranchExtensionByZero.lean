module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.LocallyConstantCoefficients.ConstantFiltration
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltrationUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleTraceDegreeSmallEtale
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImageModuleUniverse
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.IntegralHomCohomologyCollapse
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteCohomology

/-!
# Extension by zero of a locally constant sheaf from an irreducible geometrically unibranch open

Let `Λ` be a Noetherian ring, `k` an algebraically closed field, `X` a separated scheme of
finite type over `k` of dimension at most one, `j : U ⟶ X` an open immersion with `U`
irreducible and geometrically unibranch, `ℓ` a prime, `n > 0` and `G` a finite type, locally
constant sheaf of `Λ`-modules on `U_étale` killed by `ℓ ^ n`. This file runs the proof of
[Stacks, Tag 0GJH] in this situation, where its input Lemma 0GJ0 applies to `U`: `H^q(X, j_! G)`
is a finite `Λ`-module when `ℓ` is prime to the characteristic of `k` or `X` is proper. Lemma 0GJF
enters as `module_finite_cohomology_extensionByZero_constantSheaf`
with its two inputs supplied: Theorem 03SC by
`Stacks.EtaleCohomology.curveTorsionCohomologyStatement_holds` and Lemma 0GJD by
`Stacks.EtaleCohomology.TorsionModules.moduleEtaleCohomology_isIntegralHom_iso`.

## Main results

* `module_finite_cohomology_extensionByZero_of_isGeometricallyUnibranch`.

## Implementation notes

The proof is the source's. Lemma 0GJ0
(`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_finiteModuleFiltration_general`) gives a
finite étale `f : T ⟶ U` of degree `d` prime to `ℓ` and a filtration of `f^{-1} G` with constant
graded pieces. The trace (Section 03SH,
`Stacks.EtaleCohomology.exists_etaleModule_unit_comp_eq_id_of_coprime`) makes `G` a direct
summand of `f_* f^{-1} G`, so `H^q(X, j_! G)` is a direct summand of `H^q(X, j_! f_* f^{-1} G)`.
Zariski's Main Theorem (Tag 05K0) factors `T ⟶ X` as an open immersion `T ⟶ Y` followed by a
finite `f̄ : Y ⟶ X`. The source arranges `T` dense in `Y` so that `T = U ×_X Y`; here no density
is needed: `T` is open and closed in `P = U ×_X Y` by an immersion `c`, and `c_* ≅ c_!`. Then
Tag 0GJ1 (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroFiniteDirectImageIso`) identifies
`j_! f_* = j_! p_* c_*` with `f̄_* (P ⟶ Y)_! c_!`, Lemma 0GJD
(`Stacks.EtaleCohomology.TorsionModules.moduleEtaleCohomology_isIntegralHom_iso`) passes to `Y`,
and the dévissage along the filtration
(`Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_extensionByZero_of_relSeries`,
Lemma 0GJG) reduces to the constant sheaves of Lemma 0GJF.

## References

* [Stacks Project, Tag 0GJH](https://stacks.math.columbia.edu/tag/0GJH)
* [Stacks Project, Tag 0GJ0](https://stacks.math.columbia.edu/tag/0GJ0)
* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 0GJ1](https://stacks.math.columbia.edu/tag/0GJ1)
* [Stacks Project, Tag 0GJD](https://stacks.math.columbia.edu/tag/0GJD)
* [Stacks Project, Tag 0GJF](https://stacks.math.columbia.edu/tag/0GJF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u r

attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale
attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat

namespace Stacks.EtaleCohomology.TorsionModules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- A sheaf of modules killed by `m` as an object is killed by `m` sectionwise. -/
theorem nsmul_eq_zero_of_nsmul_id_eq_zero {X : Scheme.{u}} {G : EtaleModules.{u, r} Λ X}
    {m : ℕ} (h : m • 𝟙 G = 0) (V : X.Etale) (x : G.obj.obj (op V)) : m • x = 0 := by
  have h₁ : ((sheafToPresheaf _ _).map (m • 𝟙 G)).app (op V) = m • 𝟙 _ := by
    simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, NatTrans.app_nsmul,
      NatTrans.id_app]
  have h₂ := congrArg (fun φ ↦ φ x) h₁
  rw [h] at h₂
  simpa using h₂.symm

/-- A retract of a finite module is finite. -/
theorem module_finite_of_retract {R : Type*} [Ring R] {A B : ModuleCat R} (i : A ⟶ B)
    (p : B ⟶ A) (h : i ≫ p = 𝟙 A) [Module.Finite R B] : Module.Finite R A :=
  Module.Finite.of_surjective p.hom fun y => ⟨i.hom y, by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h]
    rfl⟩

/-- The lift `T ⟶ U ×_X Y` of `f : T ⟶ U` and an open immersion `T ⟶ Y` is an open immersion
when `U ⟶ X` is one. -/
theorem isOpenImmersion_pullback_lift {T U X Y : Scheme.{u}} {j : U ⟶ X} {πY : Y ⟶ X}
    [IsOpenImmersion j] (f : T ⟶ U) (j₁ : T ⟶ Y) [IsOpenImmersion j₁]
    (hfac : f ≫ j = j₁ ≫ πY) : IsOpenImmersion (pullback.lift f j₁ hfac) := by
  have : IsOpenImmersion (pullback.lift f j₁ hfac ≫ pullback.snd j πY) := by
    rw [pullback.lift_snd]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.snd j πY)

/-- The lift `T ⟶ U ×_X Y` of a finite `f : T ⟶ U` and an open immersion `T ⟶ Y` is a closed
immersion when `U ⟶ X` is an open immersion and `Y ⟶ X` is finite. -/
theorem isClosedImmersion_pullback_lift {T U X Y : Scheme.{u}} {j : U ⟶ X} {πY : Y ⟶ X}
    [IsOpenImmersion j] [IsFinite πY] (f : T ⟶ U) [IsFinite f] (j₁ : T ⟶ Y)
    [IsOpenImmersion j₁] (hfac : f ≫ j = j₁ ≫ πY) :
    IsClosedImmersion (pullback.lift f j₁ hfac) := by
  have := isOpenImmersion_pullback_lift f j₁ hfac
  have : IsFinite (pullback.lift f j₁ hfac ≫ pullback.fst j πY) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsFinite (pullback.lift f j₁ hfac) := IsFinite.of_comp _ (pullback.fst j πY)
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨‹_›, inferInstance⟩

/-- Let `X` be a separated curve of finite type over an algebraically closed field `k`,
`Y ⟶ X` finite and `i : T ⟶ Y` an open immersion. A sheaf `K` on `T_étale` killed by `ℓ ^ n`
with a filtration by constant sheaves of finite modules has `H^q(Y, i_! K)` finite when `ℓ` is
prime to the characteristic of `k` or `X` is proper. -/
theorem module_finite_cohomology_extensionByZero_of_isFinite_of_relSeries
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    {Y T : Scheme.{u}} (πY : Y ⟶ X) [IsFinite πY] (i : T ⟶ Y) [IsOpenImmersion i]
    (K : EtaleModules.{u, r} Λ T) (Xs : RelSeries (ConstantFiniteModuleStep Λ K))
    (h0 : IsZero (Subobject.underlying.obj Xs.head)) (hl : IsIso Xs.last.arrow)
    {ℓ n : ℕ} (hℓ : ℓ.Prime) (hK : ℓ ^ n • 𝟙 K = 0)
    (h : ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ i).obj K)) := by
  refine module_finite_cohomology_extensionByZero_of_relSeries Λ i K Xs h0 hl (ℓ ^ n) hK q
    fun M _ hMn => ?_
  have hY : topologicalKrullDim Y ≤ 1 :=
    le_trans (topologicalKrullDim_le_of_isIntegralHom πY) hX
  have hpos : 0 < ℓ ^ n := Nat.pow_pos hℓ.pos
  have : IsSeparated (πY ≫ π) := inferInstance
  have : LocallyOfFiniteType πY :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType πY).mp ‹_›).2
  have : LocallyOfFiniteType (πY ≫ π) := locallyOfFiniteType_comp πY π
  have : QuasiCompact (πY ≫ π) := inferInstance
  refine module_finite_cohomology_extensionByZero_constantSheaf Λ
    curveTorsionCohomologyStatement_holds.{u, r}
    (by
      intros
      exact Module.Finite.equiv
        (moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ _ _ _).toLinearEquiv)
    (πY ≫ π) hY M (ℓ ^ n) hpos hMn ?_ i q
  rcases h with h | h
  · exact .inl (h.pow_left n)
  · exact .inr inferInstance

omit [IsNoetherianRing Λ] in
/-- Let `j : U ⟶ X` be an open immersion, `πY : Y ⟶ X` finite, and `f : T ⟶ U` factor through
`U ×_X Y` by a map `c` that is both an open and a closed immersion. If `H^q(Y, (c ≫ p)_! K)` is
finite, for `p : U ×_X Y ⟶ Y` the projection, then so is `H^q(X, j_! f_* K)`. -/
theorem module_finite_cohomology_extensionByZero_directImage_of_pullback_lift
    {X Y U T : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (πY : Y ⟶ X) [IsFinite πY]
    (f : T ⟶ U) (c : T ⟶ pullback j πY) [IsOpenImmersion c] [IsClosedImmersion c]
    (hc : c ≫ pullback.fst j πY = f) (K : EtaleModules.{u, r} Λ T) (q : ℕ)
    (hK : Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ (c ≫ pullback.snd j πY)).obj K))) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((etaleModuleDirectImage.{u, r} Λ f).obj K))) := by
  let e₁ : (etaleModuleDirectImage.{u, r} Λ f).obj K ≅
      (etaleModuleDirectImage.{u, r} Λ (pullback.fst j πY)).obj
        ((etaleModuleDirectImage.{u, r} Λ c).obj K) :=
    ((etaleModuleDirectImageComp.{u, r} Λ c (pullback.fst j πY) f hc.symm).app K).symm
  let e₂ : (etaleModuleExtensionByZero.{u, r} Λ j).obj
      ((etaleModuleDirectImage.{u, r} Λ (pullback.fst j πY)).obj
        ((etaleModuleDirectImage.{u, r} Λ c).obj K)) ≅
      (etaleModuleDirectImage.{u, r} Λ πY).obj
        ((etaleModuleExtensionByZero.{u, r} Λ (pullback.snd j πY)).obj
          ((etaleModuleDirectImage.{u, r} Λ c).obj K)) :=
    (etaleModuleExtensionByZeroFiniteDirectImageIso.{u, r} Λ j (pullback.snd j πY)
    (pullback.fst j πY) πY (IsPullback.of_hasPullback j πY)).app
      ((etaleModuleDirectImage.{u, r} Λ c).obj K)
  let e₃ : (etaleModuleDirectImage.{u, r} Λ c).obj K ≅
      (etaleModuleExtensionByZero.{u, r} Λ c).obj K :=
    (etaleModuleDirectImage.{u, r} Λ c).mapIso
        ((etaleModuleExtensionByZeroIdIso Λ T).app K).symm ≪≫
      ((etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ (𝟙 T) (𝟙 T) c c
        (IsKernelPair.id_of_mono c)).app K).symm ≪≫
      (etaleModuleExtensionByZero.{u, r} Λ c).mapIso ((etaleModuleDirectImageIdIso Λ T).app K)
  let N := (etaleModuleExtensionByZero.{u, r} Λ (pullback.snd j πY)).obj
    ((etaleModuleDirectImage.{u, r} Λ c).obj K)
  let e₄ := ((etaleModuleExtensionByZeroCompIso.{u, r} Λ c (pullback.snd j πY)).app K).symm
  have : Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).obj N) :=
    Module.Finite.equiv (((etaleModuleGlobalSections.{u, r} Λ Y).rightDerived q).mapIso
      ((etaleModuleExtensionByZero.{u, r} Λ (pullback.snd j πY)).mapIso e₃ ≪≫
        e₄)).symm.toLinearEquiv
  have : Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleDirectImage.{u, r} Λ πY).obj N)) :=
    Module.Finite.equiv (moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ πY q N).toLinearEquiv
  exact Module.Finite.equiv (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).mapIso
    ((etaleModuleExtensionByZero.{u, r} Λ j).mapIso e₁ ≪≫ e₂)).symm.toLinearEquiv

/-- **[Stacks, Tag 0GJH] for an irreducible geometrically unibranch open.**
Let `X` be a separated scheme of finite type over an algebraically closed field `k` of dimension
at most one, `j : U ⟶ X` an open immersion with `U` irreducible and geometrically unibranch, and
`G` a finite type, locally constant sheaf of `Λ`-modules on `U_étale` killed by `ℓ ^ n` for a
prime `ℓ`. If `ℓ` is prime to the characteristic of `k`, or
`X` is proper over `k`, then `H^q(X, j_! G)` is a finite `Λ`-module. -/
theorem module_finite_cohomology_extensionByZero_of_isGeometricallyUnibranch
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IrreducibleSpace U]
    (hU : IsGeometricallyUnibranch U) (G : EtaleModules.{u, r} Λ U)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ U.smallEtaleTopology G)
    {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n) (hGn : ℓ ^ n • 𝟙 G = 0)
    (h : ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj G)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  set HX := (etaleModuleGlobalSections.{u, r} Λ X).rightDerived q
  -- Lemma 0GJ0 on `U`
  obtain ⟨x⟩ : Nonempty U := IrreducibleSpace.toNonempty
  let s : GeometricPoint U :=
    ⟨AlgebraicClosure (U.residueField x), Spec.map (CommRingCat.ofHom
      (algebraMap (U.residueField x) (AlgebraicClosure (U.residueField x)))) ≫
        U.fromSpecResidueField x⟩
  obtain ⟨T, f, d, hf, hfe, hrank, hd, Xs, h0, hl⟩ :=
    Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_finiteModuleFiltration_general hℓ hn
      hU s G hG (nsmul_eq_zero_of_nsmul_id_eq_zero Λ hGn)
  let K := (etaleModuleInverseImage.{u, r} Λ f).obj G
  have hK : ℓ ^ n • 𝟙 K = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hGn, Functor.map_zero]
  -- the trace makes `j_! G` a direct summand of `j_! f_* f^{-1} G`
  obtain ⟨r', hr'⟩ := exists_etaleModule_unit_comp_eq_id_of_coprime Λ f d G
    (Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hd).symm) hGn
  suffices hfin : Module.Finite Λ (HX.obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj
      ((etaleModuleDirectImage.{u, r} Λ f).obj K))) by
    have : Module.Finite Λ (HX.obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ f).obj G))) :=
      hfin
    refine module_finite_of_retract (HX.map ((etaleModuleExtensionByZero.{u, r} Λ j).map
      ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app G)))
      (HX.map ((etaleModuleExtensionByZero.{u, r} Λ j).map r')) ?_
    rw [← Functor.map_comp, ← Functor.map_comp, hr']
    exact (etaleModuleExtensionByZero.{u, r} Λ j ⋙ HX).map_id G
  -- Zariski's Main Theorem
  obtain ⟨Y, j₁, πY, hj₁, -, hπY, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization (f ≫ j)
  have := isOpenImmersion_pullback_lift f j₁ hfac
  have := isClosedImmersion_pullback_lift f j₁ hfac
  exact module_finite_cohomology_extensionByZero_directImage_of_pullback_lift Λ j πY f
    (pullback.lift f j₁ hfac) (pullback.lift_fst _ _ _) K q
    (module_finite_cohomology_extensionByZero_of_isFinite_of_relSeries Λ π hX πY
      (pullback.lift f j₁ hfac ≫ pullback.snd j πY) K Xs h0 hl hℓ hK h q)

end Stacks.EtaleCohomology.TorsionModules
