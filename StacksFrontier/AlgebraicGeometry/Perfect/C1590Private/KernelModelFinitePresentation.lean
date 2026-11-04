module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsArbitraryBase
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsKernelModel

/-!
# Global sections of base changes as the kernel of one matrix, over an arbitrary base

Let `A` be a ring, `f : X ⟶ Spec A` proper and of finite presentation, `F` an `𝒪_X`-module of
finite presentation flat over `A`, and `p` a prime of `A`. Near `p` the global sections of every
base change of `F` are the kernel of a single matrix over `A` whose entries lie in `p`, naturally
in the base change (cf. the proof of [Stacks, Tag 0BDL]).

This is `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_away_kernelModel` with its
Noetherian hypothesis removed. The proof there uses the Noetherian hypothesis only to know that
the Čech model of `RΓ(X, F)` is perfect; over an arbitrary base that is
`isPerfect_derivedGlobalSectionsOverBase_of_isProper` in the same namespace
([Stacks, Tag 0B91]), and the rest of the argument is unchanged.

## Main results

* `AlgebraicGeometry.C1590Private.exists_away_kernelModel_of_finitePresentation`: the kernel model.

## Implementation notes

An unregistered helper. The derived categories of modules are the standard models
(`CategoryTheory.HasDerivedCategory.standard`), introduced as local instances inside the proof,
because the results it combines are stated for them.

## References

* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace AlgebraicGeometry.C1590Private

/-- **Cohomology and base change in degree `0`: a minimal local kernel model, over an arbitrary
base** (cf. the proof of [Stacks, Tag 0BDL]). Let `f : X ⟶ Spec A` be proper and of finite
presentation and `F` an `𝒪_X`-module of finite presentation flat over `A`, and let `p` be a prime
of `A`. There are `g ∉ p` and a `β × r` matrix `D` over `A` with all entries in `p` such that for
every `A`-algebra `φ : A ⟶ B` in which `g` is invertible and every cartesian square exhibiting
`X'` as `X ×_A B`, the `B`-module `Γ(X', F_{X'})` is identified with `ker(D ⊗ B : B^r → B^β)`,
naturally in `B`. -/
theorem exists_away_kernelModel_of_finitePresentation {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (p : Ideal A) [p.IsPrime] :
    ∃ (g : A) (_ : g ∉ p) (r β : ℕ) (D : Matrix (Fin β) (Fin r) A) (_ : ∀ i j, D i j ∈ p)
      (Φ : ∀ {B : Type u} [CommRing B] (φ : A →+* B) (_ : IsUnit (φ g)) {X' : Scheme.{u}}
          {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
          (_ : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))),
          letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj F) ⊤
          LinearMap.ker (Matrix.mulVecLin (D.map φ)) ≃ₗ[B]
            Γ((Scheme.Modules.pullback g').obj F, ⊤)),
      ∀ {B B' : Type u} [CommRing B] [CommRing B'] (φ : A →+* B) (ψ : B →+* B')
        (hg : IsUnit (φ g)) {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)}
        {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
        (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
        (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ)))
        (v : LinearMap.ker (Matrix.mulVecLin (D.map φ))),
        ((Scheme.Modules.pullbackComp g'' g').hom.app F).app ⊤
            (AlgebraicGeometry.pullbackSectionHom g'' ((Scheme.Modules.pullback g').obj F) ⊤ ⊤
              (by simp) (Φ φ hg hsq v)) =
          Φ (ψ.comp φ) (hg.map ψ)
            (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g' g'' hsq hsq')
            ⟨ψ ∘ (v : Fin r → B), by
              have hv := v.2
              rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
              funext i
              have h := RingHom.map_mulVec ψ (D.map φ) (v : Fin r → B) i
              rw [hv, Pi.zero_apply, map_zero, Matrix.map_map] at h
              exact h.symm⟩ := by
  classical
  have : F.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation F
  let : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u} p.ResidueField) := HasDerivedCategory.standard _
  obtain ⟨I, hIfin, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  let := hIlin
  have := hIfin
  let C := baseAlternatingCechComplex f U hU F
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj C) :=
    StacksDraft.Perfect.isPerfect_of_iso
      (alternatingCechIsoDerivedGlobalSectionsOverBase f U hU F haff)
      (isPerfect_derivedGlobalSectionsOverBase_of_isProper f F hflat)
  have hpc := StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _ hperf
  let κ := p.ResidueField
  have hmodel : ∀ i : ℤ, Module.finrank κ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C))) =
      Module.finrank κ ((extendScalarsComplex (algebraMap A κ) C).homology i) := fun i =>
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU F (algebraMap A κ) hUaff hflat) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} κ) i).app _).toLinearEquiv.finrank_eq
  have hvan : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C))) := fun i hi => by
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU F (algebraMap A κ) hUaff hflat) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} κ) i).app _)
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A κ)).map_isZero
        (isZero_baseAlternatingCechComplex_X_of_neg f U hU F i hi))
  obtain ⟨g, hg, -, P, b, hPge, hPle, hPX, ⟨eP⟩⟩ :=
    StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below
      p (DerivedCategory.Q.obj C) hpc ⟨0, inferInstance⟩ 0 hvan
  let Ag := Localization.Away g
  let : HasDerivedCategory (ModuleCat.{u} Ag) := HasDerivedCategory.standard _
  let α := algebraMap A Ag
  let r := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 0).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C)))
  let β := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 1).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C)))
  have : P.IsStrictlyLE b := hPle
  have : P.IsStrictlyGE 0 := hPge
  have hproj : ∀ n, Projective (P.X n) := fun n =>
    Projective.of_iso (hPX n).some.symm
      (ModuleCat.projective_of_free (Module.Free.chooseBasis Ag _))
  have : ∀ n, Module.Flat Ag (P.X n) := fun n =>
    Module.Flat.of_linearEquiv (hPX n).some.toLinearEquiv
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective P
    (extendScalarsComplex α C)
    (eP.hom ≫ (totalDerivedExtensionScalarsModelIso f U hU F α hUaff hflat).hom)
  have : QuasiIso u := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 (by
    rw [hu]
    infer_instance)
  have hP : IsZero (P.X (-1)) := P.isZero_of_isStrictlyGE 0 (-1)
  let e₀ : P.X 0 ≅ ModuleCat.of Ag (Fin r → Ag) :=
    (hPX 0).some ≪≫ (ULift.moduleEquiv (R := Ag) (M := Fin r → Ag)).toModuleIso
  let e₁ : P.X 1 ≅ ModuleCat.of Ag (Fin β → Ag) :=
    (hPX 1).some ≪≫ (ULift.moduleEquiv (R := Ag) (M := Fin β → Ag)).toModuleIso
  let L : (Fin r → Ag) →ₗ[Ag] (Fin β → Ag) := e₁.hom.hom ∘ₗ (P.d 0 1).hom ∘ₗ e₀.inv.hom
  let M := LinearMap.toMatrix' L
  have hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv := by
    ext x
    simp [M, L]
  -- minimality: the differential vanishes over the residue field
  have hgκ : IsUnit (algebraMap A κ g) := by
    refine isUnit_iff_ne_zero.2 fun h => hg ?_
    rw [← Ideal.ker_algebraMap_residueField p]
    exact h
  let χ : Ag →+* κ := IsLocalization.Away.lift g hgκ
  have hχ : χ.comp α = algebraMap A κ := IsLocalization.Away.lift_comp g hgκ
  have : ∀ n : ℤ, Module.Flat Ag ((extendScalarsComplex α C).X n) := fun n => by
    have : Module.Flat A (C.X n) := flat_baseAlternatingCechComplex_X f U hU F hUaff hflat n
    let : Algebra A Ag := α.toAlgebra
    exact Module.Flat.baseChange A Ag (C.X n)
  have hqu : QuasiIso (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) :=
    StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat χ b (Fintype.card I : ℤ) u
  have hr0 : Module.finrank κ ((extendScalarsComplex χ P).homology 0) = r :=
    (isoOfQuasiIsoAt (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) 0).toLinearEquiv.finrank_eq.trans
      ((((HomologicalComplex.homologyFunctor _ _ 0).mapIso
        ((extendScalarsComplexCompIso α χ).app C)).toLinearEquiv.finrank_eq).trans
        ((finrank_homology_extendScalarsComplex_congr hχ C 0).trans (hmodel 0).symm))
  have hMχ : M.map χ = 0 := matrix_map_eq_zero_of_finrank hP e₀ e₁ M hM χ hr0
  -- clearing denominators
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g)
    (Finset.univ : Finset (Fin β × Fin r)) (fun ij => M ij.1 ij.2)
  have hN' : ∀ i j, ∃ a : A, α a = α (g ^ N) * M i j := fun i j => by
    obtain ⟨a, ha⟩ := hN (i, j) (Finset.mem_univ _)
    exact ⟨a, ha.trans (Algebra.smul_def _ _)⟩
  choose D₀ hD using hN'
  let D : Matrix (Fin β) (Fin r) A := D₀
  have hDp : ∀ i j, D i j ∈ p := fun i j => by
    rw [← Ideal.ker_algebraMap_residueField p, RingHom.mem_ker, ← hχ, RingHom.comp_apply, hD,
      map_mul]
    have := congrFun (congrFun hMχ i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    rw [this, mul_zero]
  have hDφ : ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g)),
      D.map φ = (φ g) ^ N • M.map (IsLocalization.Away.lift g hgφ) := fun {B} _ φ hgφ => by
    ext i j
    have h := congrArg (IsLocalization.Away.lift g hgφ) (hD i j)
    rw [← RingHom.comp_apply, IsLocalization.Away.lift_comp, map_mul, ← RingHom.comp_apply,
      IsLocalization.Away.lift_comp, map_pow] at h
    simpa [Matrix.map_apply] using h
  have hker : ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g)),
      LinearMap.ker (D.map φ).mulVecLin =
        LinearMap.ker (M.map (IsLocalization.Away.lift g hgφ)).mulVecLin := fun {B} _ φ hgφ => by
    rw [hDφ φ hgφ, ker_mulVecLin_smul _ (hgφ.pow N)]
  refine ⟨g, hg, r, β, D, hDp, fun {B} _ φ hgφ X' f' g' hsq =>
    (LinearEquiv.ofEq _ _ (hker φ hgφ)).trans
      (kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM (IsLocalization.Away.lift g hgφ)
        (by rwa [IsLocalization.Away.lift_comp])), ?_⟩
  intro B B' _ _ φ ψ hgφ X' X'' f' f'' g' g'' hsq hsq' v
  have hsq₁ : IsPullback g' f' f (Spec.map (CommRingCat.ofHom
      ((IsLocalization.Away.lift g hgφ).comp α))) := by
    rwa [IsLocalization.Away.lift_comp]
  have hcomp : ψ.comp (IsLocalization.Away.lift (S := Ag) g hgφ) =
      IsLocalization.Away.lift (S := Ag) (g := ψ.comp φ) g (hgφ.map ψ) :=
    IsLocalization.ringHom_ext (Submonoid.powers g) (by
      rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp])
  let v' := LinearEquiv.ofEq _ _ (hker φ hgφ) v
  have hsq'' : IsPullback (g'' ≫ g') f'' f (Spec.map (CommRingCat.ofHom
      ((ψ.comp (IsLocalization.Away.lift g hgφ)).comp α))) :=
    Stacks.Cech.isPullback_comp_specMap _ ψ f f' f'' g' g'' hsq₁ hsq'
  have key := kernelModelEquiv_comp α F U hU hUaff hflat u b hP e₀ e₁ M hM
    (IsLocalization.Away.lift g hgφ) ψ hsq₁ hsq' hsq'' v'
    (comp_mem_ker_mulVecLin_map M _ ψ _ v'.2)
  beta_reduce
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  convert key using 1
  have hc := kernelModelEquiv_congr α F U hU hUaff hflat u b hP e₀ e₁ M hM hcomp.symm
    (by
      rw [IsLocalization.Away.lift_comp]
      exact Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g' g'' hsq hsq')
    hsq''
    (LinearEquiv.ofEq _ _ (hker (ψ.comp φ) (hgφ.map ψ)) ⟨ψ ∘ (v : Fin r → B),
      comp_mem_ker_mulVecLin_map D φ ψ _ v.2⟩)
    ⟨ψ ∘ (v' : Fin r → B), comp_mem_ker_mulVecLin_map M _ ψ _ v'.2⟩ rfl
  convert hc using 2

end AlgebraicGeometry.C1590Private

end
