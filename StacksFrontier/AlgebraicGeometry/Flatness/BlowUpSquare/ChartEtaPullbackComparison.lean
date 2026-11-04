module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartDecalageExistence
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaChartPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackCore
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaAffineComparison
public import StacksFrontier.Homology.Eta.Perfect.LocallyFree
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect

/-!
# The décalage of an affine chart commutes with an arbitrary pullback

Let `(U, A, f, M^•)` be an affine chart of a triple `(X, D, M)` as in Situation 0F8S, all of
whose determinantal ideals `I_i(M^•, f)` are principal, and let `φ : A → B` be a ring map with
`φ(f)` a nonzerodivisor. On `Spec A` the pulled-back divisor is cut out by `f`, and the décalage
of the complex of sheaves `M̃^•` is `(η_f M^•)^~`. This file shows that pullback along
`Spec B ⟶ Spec A` preserves, in every degree, the fibre product of sheaves defining the décalage
of `M̃^•`.

Taking global sections, the defining fibre product is the fibre product of `dⁱ : M^i → M^{i+1}`
and multiplication by `f` on `M^{i+1}`, read through multiplication by `fⁱ` inside the
localizations at `f`. Extension of scalars along `φ` preserves that fibre product by
More on Algebra, Tag 0F7X, and pullback of quasi-coherent sheaves along a morphism of affine
schemes is extension of scalars of global sections. Since `(η_f M^•)^~` is moreover K-flat, the
comparison `L(Spec φ)^*[η M̃^•] ⟶ [η(Spec φ)^*M̃^•]` of décalages is an isomorphism.

## Main results

* `Stacks.Eta.LocallyFreeTerms.isIso_pullbackComparison_iff_of_fpowSub`: a fibre product of
  modules presented inside localizations at `f` by its images `fⁱ M`, `fⁱ N`, `fⁱ⁺¹ N` is
  preserved by a functor exactly when the fibre product of `d` and `f` is.
* `Stacks.Eta.LocallyFreeTerms.isIso_pullbackComparison_restrictScalars_extendScalars`: Tag 0F7X
  as preservation of a fibre product, read through a ring map.
* `AffineChart.isIso_pullbackComparison_idealPower_specTildeComplex`: pullback along
  `Spec B ⟶ Spec A` preserves the fibre products defining the décalage of `M̃^•`.
* `AffineChart.kFlat_etaComplex`: `η_f M^•` is K-flat.
* `AffineChart.isIso_derivedPullbackEtaCore_specTildeComplex`: the comparison of décalages along
  `Spec B ⟶ Spec A` at `M̃^•` is an isomorphism.

## References

* [Stacks Project, Tag 0F7X](https://stacks.math.columbia.edu/tag/0F7X)
* [Stacks Project, Tag 0F8M](https://stacks.math.columbia.edu/tag/0F8M)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Divisors.Eta (idealSheaf idealSheafι)

universe u d

namespace Stacks.Eta.LocallyFreeTerms

open EtaPow

variable {A : Type u} [CommRing A]

/-- `fⁱ M ⊆ M_f` is carried to `fⁱ N` by the localization of a linear map, and multiplication by
`fⁱ` commutes with it. -/
theorem fLoc_fpowMap {f : A} {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (d : M →ₗ[A] N) (i : ℤ) (m : M) :
    fLoc f d (fpowMap f M i m) = fpowMap f N i (d m) := by
  rw [fpowMap_apply, fpowMap_apply, fLoc_zpow_smul, fLoc_toLoc]

/-- A module embedded into `M_f` with image `fⁱ M` is identified with `M` through
multiplication by `fⁱ`. -/
theorem fpowMap_fpowEquiv_symm_ofInjective {f : A} {M P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (hM : IsSMulRegular M f) (i : ℤ)
    (Θ : P →ₗ[A] LocalizedModule.Away f M) (h : Function.Injective Θ)
    (r : LinearMap.range Θ = fpowSub f M i) (x : P) :
    fpowMap f M i ((((LinearEquiv.ofInjective Θ h).trans (LinearEquiv.ofEq _ _ r)).trans
      (fpowEquiv f hM i).symm) x) = Θ x := by
  rw [← fpowEquiv_apply f hM i]
  change (((fpowEquiv f hM i) ((fpowEquiv f hM i).symm ((LinearEquiv.ofEq _ _ r)
    ((LinearEquiv.ofInjective Θ h) x)))) : LocalizedModule.Away f M) = Θ x
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **The fibre product of the décalage, presented inside localizations.** Let `a : P₁ ⟶ P₂` and
`b : P₃ ⟶ P₂` be maps of `A`-modules, and suppose `P₁`, `P₂`, `P₃` embed into `M_f`, `N_f`, `N_f`
with images `fⁱ M`, `fⁱ N` and `fⁱ⁺¹ N`, compatibly with `a` (through the localization of
`d : M → N`) and `b` (through the inclusion). If `f` is a nonzerodivisor on `M` and `N`, a functor
preserves the fibre product of `a` and `b` exactly when it preserves the fibre product of `d` and
multiplication by `f` on `N`: the two cospans are isomorphic, through multiplication by `fⁱ`. -/
theorem isIso_pullbackComparison_iff_of_fpowSub {D : Type*} [Category D] [HasPullbacks D]
    (G : ModuleCat.{u} A ⥤ D) (f : A) {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (hM : IsSMulRegular M f) (hN : IsSMulRegular N f)
    (d : M →ₗ[A] N) (i : ℤ) {P₁ P₂ P₃ : ModuleCat.{u} A} (a : P₁ ⟶ P₂) (b : P₃ ⟶ P₂)
    (Θ₁ : P₁ →ₗ[A] LocalizedModule.Away f M) (Θ₂ : P₂ →ₗ[A] LocalizedModule.Away f N)
    (Θ₃ : P₃ →ₗ[A] LocalizedModule.Away f N)
    (h₁ : Function.Injective Θ₁) (h₂ : Function.Injective Θ₂) (h₃ : Function.Injective Θ₃)
    (r₁ : LinearMap.range Θ₁ = fpowSub f M i) (r₂ : LinearMap.range Θ₂ = fpowSub f N i)
    (r₃ : LinearMap.range Θ₃ = fpowSub f N (i + 1))
    (ha : Θ₂ ∘ₗ a.hom = fLoc f d ∘ₗ Θ₁) (hb : Θ₂ ∘ₗ b.hom = Θ₃) :
    IsIso (pullbackComparison G a b) ↔
      IsIso (pullbackComparison G (ModuleCat.ofHom d : ModuleCat.of A M ⟶ ModuleCat.of A N)
        (ModuleCat.ofHom (f • LinearMap.id) : ModuleCat.of A N ⟶ ModuleCat.of A N)) := by
  have key : ∀ {M' : Type u} [AddCommGroup M'] [Module A M'] (hM' : IsSMulRegular M' f) (j : ℤ)
      {P : ModuleCat.{u} A} (Θ : P →ₗ[A] LocalizedModule.Away f M') (h : Function.Injective Θ)
      (r : LinearMap.range Θ = fpowSub f M' j), ∃ e : P ≃ₗ[A] M', ∀ x, fpowMap f M' j (e x) = Θ x :=
    @fun _ _ _ hM' j _ Θ h r => ⟨_, fpowMap_fpowEquiv_symm_ofInjective hM' j Θ h r⟩
  obtain ⟨e₁, he₁⟩ := key hM i Θ₁ h₁ r₁
  obtain ⟨e₂, he₂⟩ := key hN i Θ₂ h₂ r₂
  obtain ⟨e₃, he₃⟩ := key hN (i + 1) Θ₃ h₃ r₃
  refine isIso_pullbackComparison_iff_of_isIso G a b _ _ e₁.toModuleIso.hom e₃.toModuleIso.hom
    e₂.toModuleIso.hom ?_ ?_
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => fpowMap_injective f hN i ?_)
    change fpowMap f N i (e₂ (a.hom x)) = fpowMap f N i (d (e₁ x))
    rw [he₂, ← fLoc_fpowMap, he₁]
    exact LinearMap.congr_fun ha x
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => fpowMap_injective f hN i ?_)
    change fpowMap f N i (e₂ (b.hom x)) = fpowMap f N i (f • e₃ x)
    rw [he₂, ← fpowMap_succ, he₃]
    exact LinearMap.congr_fun hb x

/-- **Tag 0F7X, read through a ring isomorphism.** Let `σ : A → A'` and `φ : A → B` be ring maps,
and let `δ : M₀ → M₁` be a map of `A'`-modules which, read through `σ`, is the differential
`dⁿ` of a bounded complex `M^•` of finite free `A`-modules satisfying the hypotheses of Tag 0F7X.
Then restriction of scalars along `σ` followed by extension of scalars along `φ` preserves the
fibre product of `δ` and multiplication by `σ f` on `M₁`. -/
theorem isIso_pullbackComparison_restrictScalars_extendScalars {A' B : Type u} [CommRing A']
    [CommRing B] (σ : A →+* A') (φ : A →+* B) (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hg : IsRegular (φ f)) (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) (n : ℤ)
    {M₀ M₁ : Type u} [AddCommGroup M₀] [Module A' M₀] [AddCommGroup M₁] [Module A' M₁]
    (δ : M₀ →ₗ[A'] M₁)
    (e₀ : (ModuleCat.restrictScalars σ).obj (ModuleCat.of A' M₀) ≅
      ModuleCat.of A (Fin (C.rank n) → A))
    (e₁ : (ModuleCat.restrictScalars σ).obj (ModuleCat.of A' M₁) ≅
      ModuleCat.of A (Fin (C.rank (n + 1)) → A))
    (he : (ModuleCat.restrictScalars σ).map (ModuleCat.ofHom δ) ≫ e₁.hom =
      e₀.hom ≫ ModuleCat.ofHom (C.d n).mulVecLin) :
    IsIso (pullbackComparison (ModuleCat.restrictScalars σ ⋙ ModuleCat.extendScalars φ)
      (ModuleCat.ofHom δ : ModuleCat.of A' M₀ ⟶ ModuleCat.of A' M₁)
      (ModuleCat.ofHom (σ f • LinearMap.id) : ModuleCat.of A' M₁ ⟶ ModuleCat.of A' M₁)) := by
  rw [pullbackComparison_comp]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  refine (isIso_pullbackComparison_iff_of_isIso (ModuleCat.extendScalars φ) _ _
    (ModuleCat.ofHom (C.d n).mulVecLin) (ModuleCat.ofHom (f • LinearMap.id))
    e₀.hom e₁.hom e₁.hom he ?_).2
    (isIso_pullbackComparison_extendScalars_mulVecLin φ C f hf hg hI n)
  exact ModuleCat.hom_ext (LinearMap.ext fun x => map_smul e₁.hom.hom f x)

/-- A module over `A'` which, read through `σ : A → A'`, is finite free over `A` has no
`σ f`-torsion when `f` is a nonzerodivisor of `A`. -/
theorem isSMulRegular_of_restrictScalars_iso {A' : Type u} [CommRing A'] (σ : A →+* A')
    {P : ModuleCat.{u} A'} {r : ℕ}
    (e : (ModuleCat.restrictScalars σ).obj P ≅ ModuleCat.of A (Fin r → A)) {f : A}
    (hf : IsRegular f) : IsSMulRegular P (σ f) := by
  intro x y hxy
  apply e.toLinearEquiv.injective
  apply (hf.isSMulRegular : IsSMulRegular (Fin r → A) f)
  change f • e.toLinearEquiv x = f • e.toLinearEquiv y
  let x' : (ModuleCat.restrictScalars σ).obj P := x
  let y' : (ModuleCat.restrictScalars σ).obj P := y
  have hxy' : f • x' = f • y' := hxy
  calc f • e.toLinearEquiv x = e.toLinearEquiv (f • x') := (e.toLinearEquiv.map_smul f x').symm
    _ = e.toLinearEquiv (f • y') := congrArg e.toLinearEquiv hxy'
    _ = f • e.toLinearEquiv y := e.toLinearEquiv.map_smul f y'

end Stacks.Eta.LocallyFreeTerms

namespace AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

/-- Global sections on `Spec R`, as `R`-modules, are sections over `⊤` with scalars restricted
along `Γ(Spec R, ⊤) ≅ R`; so a functor preserves the fibre product of the global sections of a
cospan exactly when it preserves the fibre product of its sections over `⊤`. -/
theorem isIso_pullbackComparison_moduleSpecΓFunctor_iff {R : CommRingCat.{u}} {D : Type*}
    [Category D] [HasPullbacks D] (G : ModuleCat.{u} R ⥤ D) {M N P : (Spec R).Modules}
    (a : M ⟶ P) (b : N ⟶ P) :
    IsIso (pullbackComparison G (moduleSpecΓFunctor.map a) (moduleSpecΓFunctor.map b)) ↔
      IsIso (pullbackComparison G
        ((Stacks.IdealTorsion.Eta.sectionsFunctor (Spec R).toRingedSpace ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).map a)
        ((Stacks.IdealTorsion.Eta.sectionsFunctor (Spec R).toRingedSpace ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).map b)) := by
  rw [Stacks.Divisors.Eta.moduleSpecGammaFunctor_eq]

end AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

attribute [local instance] AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor

namespace AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- The modules of sections over `⊤` of the terms of `M̃^•` have no `f`-torsion. -/
theorem isSMulRegular_sections_specTildeComplex (C : AffineChart S) (k : ℤ) :
    IsSMulRegular
      ((Stacks.IdealTorsion.Eta.sectionsFunctor (Spec Γ(S.X, C.U)).toRingedSpace ⊤).obj
        (C.specTildeComplex.X k)) ((Scheme.ΓSpecIso Γ(S.X, C.U)).inv.hom C.f) :=
  Stacks.Eta.LocallyFreeTerms.isSMulRegular_of_restrictScalars_iso
    (Scheme.ΓSpecIso Γ(S.X, C.U)).inv.hom
    ((HomologicalComplex.eval _ _ k).mapIso C.gammaSpecTildeComplexIso) C.regular

/-- **Tag 0F7X on the sections of `M̃^•`.** Restriction of scalars to `A` followed by extension
of scalars along `φ` preserves the fibre product of `dⁿ` and multiplication by `f` on the modules
of sections over `⊤` of `M̃^•`. -/
theorem isIso_pullbackComparison_sections_specTildeComplex (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) {B : CommRingCat.{u}}
    (φ : Γ(S.X, C.U) ⟶ B) (hφ : IsRegular (φ.hom C.f)) (n : ℤ) :
    let E := Stacks.IdealTorsion.Eta.sectionsFunctor (Spec Γ(S.X, C.U)).toRingedSpace ⊤
    let F := C.specTildeComplex
    let σ := (Scheme.ΓSpecIso Γ(S.X, C.U)).inv.hom
    IsIso (pullbackComparison ((ModuleCat.restrictScalars.{u} σ :
        ModuleCat.{u} ((Spec Γ(S.X, C.U)).toRingedSpace.presheaf.obj (op ⊤)) ⥤
          ModuleCat.{u} Γ(S.X, C.U)) ⋙ ModuleCat.extendScalars.{u, u, u} φ.hom)
      (ModuleCat.ofHom (E.map (F.d n (n + 1))).hom :
        ModuleCat.of _ (E.obj (F.X n)) ⟶ ModuleCat.of _ (E.obj (F.X (n + 1))))
      (ModuleCat.ofHom (σ C.f • LinearMap.id) :
        ModuleCat.of _ (E.obj (F.X (n + 1))) ⟶ ModuleCat.of _ (E.obj (F.X (n + 1))))) :=
  Stacks.Eta.LocallyFreeTerms.isIso_pullbackComparison_restrictScalars_extendScalars _
    φ.hom C.complex C.f C.regular hφ hI n _
    ((HomologicalComplex.eval _ _ n).mapIso C.gammaSpecTildeComplexIso)
    ((HomologicalComplex.eval _ _ (n + 1)).mapIso C.gammaSpecTildeComplexIso)
    (by
      have h := C.gammaSpecTildeComplexIso.hom.comm n (n + 1)
      rw [BoundedComplex.toCochainComplex_d] at h
      exact h.symm)

/-- **Pullback along a morphism of affine schemes preserves the fibre products defining the
décalage of an affine chart.** Let `(U, A, f, M^•)` be an affine chart with principal
determinantal ideals and `φ : A → B` a ring map with `φ f` a nonzerodivisor. On `Spec A`, in every
degree `n`, pullback along `Spec B ⟶ Spec A` preserves the fibre product of
`I^n ⊗ M̃^n ⟶ I^n ⊗ M̃^{n+1} ⟵ I^{n+1} ⊗ M̃^{n+1}`, where `I` is the ideal sheaf of the
pulled-back divisor. On global sections the cospan is, through multiplication by `fⁿ`, the
cospan of `dⁿ` and `f`, which extension of scalars preserves by Tag 0F7X. -/
theorem isIso_pullbackComparison_idealPower_specTildeComplex (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) {B : CommRingCat.{u}}
    (φ : Γ(S.X, C.U) ⟶ B) (hφ : IsRegular (φ.hom C.f)) (n : ℤ) :
    IsIso (pullbackComparison (Scheme.Modules.pullback (Spec.map φ))
      (Stacks.IdealTorsion.Eta.idealPowerMap (Spec Γ(S.X, C.U)).toRingedSpace
        (idealSheaf (S.D.comap C.U.2.fromSpec)) n (C.specTildeComplex.d n (n + 1)))
      (Stacks.IdealTorsion.Eta.idealPowerIncl (Spec Γ(S.X, C.U)).toRingedSpace
        (idealSheaf (S.D.comap C.U.2.fromSpec)) (idealSheafι (S.D.comap C.U.2.fromSpec)) n
        (C.specTildeComplex.X (n + 1)))) := by
  let R := Γ(S.X, C.U)
  let X' := (Spec R).toRingedSpace
  let I := idealSheaf (S.D.comap C.U.2.fromSpec)
  let ι := idealSheafι (S.D.comap C.U.2.fromSpec)
  let F := C.specTildeComplex
  obtain ⟨g, hg, hgf⟩ := C.exists_generatesIdealOn_fromSpec
  let σ := (Scheme.ΓSpecIso R).inv.hom
  let f' := Stacks.IdealTorsion.Eta.generatorSection X' ι ⊤ g
  have hI' : I.IsQuasicoherent :=
    Stacks.Divisors.Eta.isQuasicoherent_of_isInvertible I inferInstance
  have hq : ∀ k : ℤ, (F.X k).IsQuasicoherent := fun k =>
    (inferInstance : ((tilde.functor R).obj (C.complex.toCochainComplex.X k)).IsQuasicoherent)
  have hq₁ := Stacks.Divisors.Eta.isQuasicoherent_idealPowerTerm I hI' (F.X n) (hq n) n
  have hq₂ := Stacks.Divisors.Eta.isQuasicoherent_idealPowerTerm I hI' _ (hq (n + 1)) (n + 1)
  have hq₃ := Stacks.Divisors.Eta.isQuasicoherent_idealPowerTerm I hI' _ (hq (n + 1)) n
  refine @isIso_pullbackComparison_pullback_spec_map_of_isQuasicoherent _ _ φ _ _ _ _ _
    hq₁ hq₂ hq₃ ?_
  let E := Stacks.IdealTorsion.Eta.sectionsFunctor X' ⊤
  let rS : ModuleCat.{u} (X'.presheaf.obj (op ⊤)) ⥤ ModuleCat.{u} R :=
    ModuleCat.restrictScalars.{u} σ
  let eS : ModuleCat.{u} R ⥤ ModuleCat.{u} B := ModuleCat.extendScalars.{u, u, u} φ.hom
  let a := Stacks.IdealTorsion.Eta.idealPowerMap X' I n (F.d n (n + 1))
  let b := Stacks.IdealTorsion.Eta.idealPowerIncl X' I ι n (F.X (n + 1))
  refine (isIso_pullbackComparison_moduleSpecΓFunctor_iff eS _ _).2 ?_
  rw [Functor.comp_map, Functor.comp_map]
  have htf := C.isIdealTorsionFree_specTildeComplex
  have hM : ∀ k, IsSMulRegular (E.obj (F.X k)) f' := fun k => by
    rw [show f' = σ C.f from hgf]
    exact C.isSMulRegular_sections_specTildeComplex k
  have ha := fun z =>
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap_natural X' I ι (F.d n (n + 1)) ⊤ g hg n z).symm
  have hb := fun z =>
    Stacks.IdealTorsion.Eta.idealPowerSectionsMap_succ X' I ι (F.X (n + 1)) ⊤ g hg n z
  have key := Stacks.Eta.LocallyFreeTerms.isIso_pullbackComparison_iff_of_fpowSub (rS ⋙ eS) f'
    (hM n) (hM (n + 1)) (E.map (F.d n (n + 1))).hom n (E.map a) (E.map b)
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap X' I ι (F.X n) ⊤ g hg n)
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap X' I ι (F.X (n + 1)) ⊤ g hg n)
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap X' I ι (F.X (n + 1)) ⊤ g hg (n + 1))
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap_injective X' I ι _ (htf n) ⊤ g hg n)
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap_injective X' I ι _ (htf (n + 1)) ⊤ g hg n)
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap_injective X' I ι _ (htf (n + 1)) ⊤ g hg
      (n + 1))
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap_range X' I ι _ ⊤ g hg n)
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap_range X' I ι _ ⊤ g hg n)
    (Stacks.IdealTorsion.Eta.idealPowerSectionsMap_range X' I ι _ ⊤ g hg (n + 1))
    (LinearMap.ext ha) (LinearMap.ext hb)
  have key3 := key.2 (by
    rw [show f' = σ C.f from hgf]
    exact C.isIso_pullbackComparison_sections_specTildeComplex hI φ hφ n)
  rw [pullbackComparison_comp] at key3
  exact IsIso.of_isIso_comp_left (eS.map (pullbackComparison rS (E.map a) (E.map b))) _

/-- The décalage `η_f M^•` of an affine chart with principal determinantal ideals is a K-flat
complex: it is bounded above, because `M^•` is bounded, and its terms are finite projective by
Tag 0F7W, hence flat. -/
theorem kFlat_etaComplex (C : AffineChart S) (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) :
    CochainComplex.KFlat.{u, u} C.etaComplex := by
  obtain ⟨b, hb⟩ := C.complex.bounded.bddAbove
  have hle : C.etaComplex.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact C.isZero_etaComplex_X <| of_not_not fun hcon => not_le_of_gt hi (hb hcon)
  have hflat : ∀ i : ℤ, Module.Flat Γ(S.X, C.U) (C.etaComplex.X i) := fun i =>
    have := (C.finite_projective_etaComplex_X hI i).2
    inferInstance
  exact CochainComplex.KFlat.kFlat_of_flat _ b

/-- **The comparison of décalages along a morphism of affine schemes is an isomorphism on an
affine chart.** Let `(U, A, f, M^•)` be an affine chart with principal determinantal ideals,
`j : Spec A ⟶ X` its open immersion and `φ : A → B` a ring map with `φ f` a nonzerodivisor. Then
the comparison `L(Spec φ)^*[η_{j^*I} M̃^•] ⟶ [η(Spec φ^* M̃^•)]` of
`Stacks.IdealTorsion.Eta.derivedPullbackEtaCore` is an isomorphism, where `I` is the ideal sheaf of
`D`.

The décalage of `M̃^•` is `(η_f M^•)^~`, which is K-flat by Tag 0F7W, and pullback along
`Spec B ⟶ Spec A` preserves its defining fibre products by
`isIso_pullbackComparison_idealPower_specTildeComplex`; both statements are transported from the
ideal sheaf of the pulled-back divisor to `j^*I` along `j^*I ≅ I_{j^{-1}D}`. -/
theorem isIso_derivedPullbackEtaCore_specTildeComplex (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) {B : CommRingCat.{u}}
    (φ : Γ(S.X, C.U) ⟶ B) (hφ : IsRegular (φ.hom C.f))
    (hm : Mono (Stacks.IdealTorsion.Eta.pullbackIdealIncl (Spec.map φ).toLRSHom.toShHom
      ((Stacks.RingedSpace.pullbackFunctor C.U.2.fromSpec.toLRSHom.toShHom).obj (idealSheaf S.D))
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl C.U.2.fromSpec.toLRSHom.toShHom
        (idealSheaf S.D) (idealSheafι S.D))))
    (hF : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree (Spec Γ(S.X, C.U)).toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl C.U.2.fromSpec.toLRSHom.toShHom
        (idealSheaf S.D) (idealSheafι S.D)) (C.specTildeComplex.X n))
    (hF' : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree (Spec B).toRingedSpace
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl (Spec.map φ).toLRSHom.toShHom
        ((Stacks.RingedSpace.pullbackFunctor C.U.2.fromSpec.toLRSHom.toShHom).obj
          (idealSheaf S.D))
        (Stacks.IdealTorsion.Eta.pullbackIdealIncl C.U.2.fromSpec.toLRSHom.toShHom
          (idealSheaf S.D) (idealSheafι S.D)))
      ((Stacks.IdealTorsion.Eta.pullbackComplex (Spec.map φ).toLRSHom.toShHom
        C.specTildeComplex).X n)) :
    IsIso (@Stacks.IdealTorsion.Eta.derivedPullbackEtaCore _ _ (Spec.map φ).toLRSHom.toShHom
      ((Stacks.RingedSpace.pullbackFunctor C.U.2.fromSpec.toLRSHom.toShHom).obj (idealSheaf S.D))
      (Stacks.IdealTorsion.Eta.pullbackIdealIncl C.U.2.fromSpec.toLRSHom.toShHom
        (idealSheaf S.D) (idealSheafι S.D))
      (@Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl _ _ C.U.2.fromSpec.toLRSHom.toShHom
        C.isFlat_fromSpec (idealSheaf S.D) (idealSheafι S.D)
        (Stacks.Divisors.Eta.mono_idealSheafι S.D))
      (Stacks.IdealTorsion.Eta.isInvertible_pullbackIdeal C.U.2.fromSpec.toLRSHom.toShHom
        (idealSheaf S.D)) hm C.specTildeComplex hF hF') := by
  have hm₀ := @Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl _ _ C.U.2.fromSpec.toLRSHom.toShHom
    C.isFlat_fromSpec (idealSheaf S.D) (idealSheafι S.D) (Stacks.Divisors.Eta.mono_idealSheafι S.D)
  have hD := C.isPullbackDefined_fromSpec
  let e := Stacks.Divisors.pullbackIdealSheafComapIso C.U.2.fromSpec S.D hD
  have he := Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι C.U.2.fromSpec S.D hD
  have hinv := Stacks.IdealTorsion.Eta.isInvertible_pullbackIdeal
    C.U.2.fromSpec.toLRSHom.toShHom (idealSheaf S.D)
  refine @Stacks.IdealTorsion.Eta.isIso_derivedPullbackEtaCore_of_kFlat_of_isIso_pullbackComparison
    _ _ _ _ _ hm₀ hinv hm _ hF hF' ?_ fun n => ?_
  · exact CochainComplex.KFlatBifunctor.KFlat.of_iso _
      (Stacks.TildeStalk.kFlatComplex_tilde Γ(S.X, C.U) C.etaComplex (C.kFlat_etaComplex hI))
      ((@Stacks.IdealTorsion.Eta.IdealCongr.etaIso (Spec Γ(S.X, C.U)).toRingedSpace _
        (idealSheaf (S.D.comap C.U.2.fromSpec)) hinv _ _ (idealSheafι (S.D.comap C.U.2.fromSpec))
        e he _ hm₀ _ hF C.isIdealTorsionFree_specTildeComplex) ≪≫
          C.etaObjSpecTildeComplexIso).symm
  · exact (Stacks.IdealTorsion.Eta.isIso_pullbackComparison_idealCongr_iff
      (Stacks.RingedSpace.pullbackFunctor (Spec.map φ).toLRSHom.toShHom) _ _ _
      (idealSheafι (S.D.comap C.U.2.fromSpec)) e he C.specTildeComplex n).2
      (C.isIso_pullbackComparison_idealPower_specTildeComplex hI φ hφ n)

end AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

end
