module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.AffineQuotient.FppfSheafPoints

/-!
# Finite flat equivalence relations over a local invariant ring

Rank and finite local freeness of the spectrum of a module-finite algebra with a basis, the
comparison `A ⊗_C A ≅ B` for a semilocal object ring with a basis chosen among the images of the
target map, flat local base changes with infinite residue field, and finiteness of the maximal
spectrum of the object ring over a local invariant ring. Together these produce, over a local
invariant ring, a basis of the object ring (Tag 03C8) making the comparison map an isomorphism.
This is the core of the argument for Tag 03BM.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Morphisms AlgebraicGeometry.GroupoidScheme

private lemma local_rank_iso_of_local_generators
    {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (G : (M.over U).GeneratingSections) (r : ℕ)
    (hG : IsIso G.π) (hr : Nonempty (G.I ≃ Fin r)) :
    Nonempty (M.restrict U.ι ≅ SheafOfModules.free (ULift (Fin r))) := by
  let : IsIso G.π := hG
  let E := Scheme.Modules.overEquiv U
  let F := E.functor
  let : F.IsLeftAdjoint := Equivalence.isLeftAdjoint_functor E
  have hpres : Limits.PreservesColimitsOfShape.{u, u} (Discrete G.I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  let unitOver := SheafOfModules.over (SheafOfModules.unit X.ringCatSheaf) U
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ F.obj unitOver :=
    (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm
  let e₁ := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F G.I hpres η
  let e₂ := F.mapIso (asIso G.π)
  let e₃ := (Scheme.Modules.overFunctorEquiv U).app M
  let e₄ : SheafOfModules.free G.I ≅ SheafOfModules.free (ULift (Fin r)) :=
    (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
      ((Classical.choice hr).trans Equiv.ulift.symm).toIso
  exact ⟨e₃.symm ≪≫ e₂.symm ≪≫ e₁.symm ≪≫ e₄⟩

private lemma scheme_modules_rank_of_card_rank {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    M.IsFiniteLocallyFreeOfRank r := by
  intro x
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨i, hi⟩ :=
    (Opens.coversTop_iff (T := X) q.X).mp q.coversTop |>.exists_mem x
  exact ⟨q.X i, hi, local_rank_iso_of_local_generators M (q.generators i) r
    (hfree.isIso i) (hrank i)⟩

private lemma module_rank_of_card_rank_on_spec
    (R : CommRingCat.{u}) (M : (Spec R).Modules) (r : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    Module.IsFiniteLocallyFreeOfRank R
      ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) r := by
  let hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r
  let : SheafOfModules.IsLocallyFree.{u, u, u} M := by
    obtain ⟨q, hq, -⟩ := hflf.exists_isFiniteLocallyFreeData
    exact SheafOfModules.IsLocallyFree.mk (M := M) ⟨q, hq⟩
  let : SheafOfModules.IsQuasicoherent.{u, u, u} M := by
    let hlf : SheafOfModules.IsLocallyFree.{u, u, u} M := inferInstance
    let q := hlf.exists_isLocallyFreeData.choose
    let : q.IsLocallyFreeData := hlf.exists_isLocallyFreeData.choose_spec
    exact q.quasiCoherentData.isQuasicoherent
  let : IsIso M.fromTildeΓ := inferInstance
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  let e : AlgebraicGeometry.tilde (R := R) (ModuleCat.of R N) ≅ M :=
    asIso M.fromTildeΓ
  exact (tilde_isFiniteLocallyFreeOfRank_iff R N r).mp
    (scheme_rank_transport_iso e.symm r (scheme_modules_rank_of_card_rank M r))

private noncomputable def specMap_pushforward_iso
    (R S : CommRingCat.{u}) (φ : R ⟶ S) :
    Stacks.Morphisms.pushforwardStructureSheaf (Spec.map φ) ≅
      AlgebraicGeometry.tilde
        ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) :=
    (Scheme.Modules.pushforward (Spec.map φ)).mapIso
      (AlgebraicGeometry.tildeSelf (R := S)).symm ≪≫
    (AlgebraicGeometry.pushforwardTildeIso R S φ).app
      (ModuleCat.of S S)

private lemma cardFiniteLocallyFree_of_moduleBasis
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M) :
    Module.IsFiniteLocallyFree R M := by
  let : Module.Free R M := Module.Free.of_basis b
  let : Module.Finite R M := Module.Finite.of_basis b
  let : Module.Projective R M := Module.Projective.of_free
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have hflat : Module.Flat R M := inferInstance
  have hcover : ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
        Module.Finite (Localization.Away f) (LocalizedModule.Away f M) :=
    (Module.finite_projective_tfae R M).out 2 7
      (a := Module.Finite R M ∧ Module.Projective R M)
      (b := ∃ s : Set R, Ideal.span s = ⊤ ∧
        ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Finite (Localization.Away f) (LocalizedModule.Away f M)).mp
      ⟨Module.Finite.of_basis b, Module.Projective.of_free⟩
  obtain ⟨s, hs, hloc⟩ := hcover
  exact ⟨s, Subtype.val, by simpa using hs, fun f ↦ hloc f f.property⟩

private lemma sheafFiniteLocallyFree_of_iso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree N := by
  obtain ⟨q, hfree, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  let q' : SheafOfModules.LocalGeneratorsData.{u} N := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators := fun i => (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have hfree' : q'.IsLocallyFreeData := by
    constructor
    intro i
    dsimp [q']
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    exact IsIso.comp_isIso' (hfree.isIso i) (inferInstance)
  have hfinite' : q'.IsFiniteType := by
    constructor
    intro i
    let := hfinite.isFiniteType i
    infer_instance
  exact ⟨q', hfree', hfinite'⟩

lemma specMap_isFiniteLocallyFree_of_moduleBasis
    (R S : CommRingCat.{u}) (φ : R ⟶ S) {n : ℕ}
    (b : letI := φ.hom.toAlgebra; Module.Basis (Fin n) R S) :
    Stacks.Morphisms.IsFiniteLocallyFree (Spec.map φ) := by
  let : Algebra R S := φ.hom.toAlgebra
  let : Module.Free R S := Module.Free.of_basis b
  let : Module.Finite R S := Module.Finite.of_basis b
  let : Module.Projective R S := Module.Projective.of_free
  let : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
  have hfp : Algebra.FinitePresentation R S :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := R) (S := S)).mp
      inferInstance
  have hfin : φ.hom.Finite := Module.Finite.of_basis b
  have hflat : φ.hom.Flat := inferInstanceAs (Module.Flat R S)
  apply (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    (Spec.map φ)).2
  rw [IsFinite.SpecMap_iff, Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff]
  exact ⟨hfin, hflat, hfp⟩

private lemma specMap_module_rank_of_ranked_finiteLocallyFree
    (R S : CommRingCat.{u}) (φ : R ⟶ S) (r : ℕ)
    [h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Spec.map φ) r] :
    letI := φ.hom.toAlgebra
    Module.IsFiniteLocallyFreeOfRank R S r := by
  let : Algebra R S := φ.hom.toAlgebra
  let M := Stacks.Morphisms.pushforwardStructureSheaf (Spec.map φ)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r :=
    h.toIsFiniteLocallyFreeOfRank
  exact (tilde_isFiniteLocallyFreeOfRank_iff R
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)) r).mp
    (scheme_rank_transport_iso (specMap_pushforward_iso R S φ) r
      (scheme_modules_rank_of_card_rank M r))

private lemma tensorProduct_equiv_arrowRing_of_semilocal_basis
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsLocalRing (invariantRing G)]
    [Infinite (IsLocalRing.ResidueField (invariantRing G))]
    {r : ℕ}
    (hAsemilocal : Finite (MaximalSpectrum Γ(G.objects.left, ⊤)))
    (hA : Ideal.map (algebraMap (invariantRing G) Γ(G.objects.left, ⊤))
      (IsLocalRing.maximalIdeal (invariantRing G)) ≤
        Ring.jacobson Γ(G.objects.left, ⊤))
    (hfinite : letI := (sourceMap G).toAlgebra
      Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤))
    (hflat : letI := (sourceMap G).toAlgebra
      Module.Flat Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤))
    (hrank : letI := (sourceMap G).toAlgebra
      ∀ P : MaximalSpectrum Γ(G.objects.left, ⊤),
      Module.finrank (Γ(G.objects.left, ⊤) ⧸ P.asIdeal)
        ((Γ(G.objects.left, ⊤) ⧸ P.asIdeal) ⊗[Γ(G.objects.left, ⊤)]
          Γ(G.arrows.left, ⊤)) = r)
    (hspan : letI := (sourceMap G).toAlgebra
      Submodule.span Γ(G.objects.left, ⊤) (Set.range (targetMap G)) = ⊤) :
    let A := Γ(G.objects.left, ⊤)
    let B := Γ(G.arrows.left, ⊤)
    let C := invariantRing G
    letI : Algebra A B := (sourceMap G).toAlgebra
    letI : Algebra C A := C.subtype.toAlgebra
    ∃ n, ∃ _bC : Module.Basis (Fin n) C A,
      ∃ e : RingEquiv (A ⊗[C] A) B,
        ∀ a a', e (a ⊗ₜ[C] a') = sourceMap G a * targetMap G a' := by
  classical
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let C := invariantRing G
  let : Algebra C A := C.subtype.toAlgebra
  let : Algebra A B := (sourceMap G).toAlgebra
  let : Module.Finite A B := hfinite
  let : Module.Flat A B := hflat
  let : Module.Free A B := Module.free_of_flat_of_finrank_eq A B r hrank
  let : Algebra C B := (sourceMap G).comp C.subtype |>.toAlgebra
  let hTower : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq' rfl
  let N : Submodule C B := LinearMap.range (targetAlgHom G).toLinearMap
  have hNset : (N : Set B) = Set.range (targetMap G) := by
    ext b
    show (∃ y, targetAlgHom G y = b) ↔ ∃ y, targetMap G y = b
    rfl
  have hN : GeneratesAsSModule A N := by
    rw [GeneratesAsSModule, hNset]
    exact hspan
  obtain ⟨n, b, hb⟩ := @contains_sBasis_of_generates C A B
    _ _ _ _ _ _ hTower _ _ hAsemilocal hA _ _ N hN
  have hx : ∀ i, ∃ a, targetMap G a = b i := fun i ↦ by
    rw [← Set.mem_range, ← hNset]
    exact hb i
  choose x hx using hx
  have hb' : ∀ i, b i = targetMap G (x i) := fun i ↦ (hx i).symm
  obtain ⟨bC, hbC⟩ := AlgebraicGeometry.basis_over_invariantRing G x ⟨b, hb'⟩
  obtain ⟨e, he⟩ := AlgebraicGeometry.tensorProduct_equiv_arrowRing G x ⟨b, hb'⟩
  exact ⟨n, bC, e, he⟩

theorem exists_flat_local_algebra_with_infinite_residueField
    (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : IsLocalRing R')
      (_ : IsLocalHom (algebraMap R R')) (_hflat : Module.Flat R R')
      (_ : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
        IsLocalRing.maximalIdeal R')
    (_ : Nonempty
        (IsLocalRing.ResidueField R' ≃ₐ[IsLocalRing.ResidueField R]
          RatFunc (IsLocalRing.ResidueField R))),
      Infinite (IsLocalRing.ResidueField R') := by
  let K := RatFunc (IsLocalRing.ResidueField R)
  let P := Polynomial (IsLocalRing.ResidueField R)
  let powers : ℕ → P := fun n => Polynomial.X ^ n
  have hpowers : Function.Injective powers := fun m n h ↦ by
    simpa only [powers, Polynomial.natDegree_X_pow] using congrArg Polynomial.natDegree h
  have : Infinite P := Infinite.of_injective powers hpowers
  let : Infinite K := Infinite.of_injective (algebraMap P K)
    (RatFunc.algebraMap_injective (IsLocalRing.ResidueField R))
  obtain ⟨R', hComm, hAlg, hLocal, hLocalHom, hflat, hmax, hres⟩ :=
    IsLocalRing.exists_flat_residueField_algEquiv R K
  let : CommRing R' := hComm
  let : Algebra R R' := hAlg
  let : IsLocalRing R' := hLocal
  let : IsLocalHom (algebraMap R R') := hLocalHom
  refine ⟨R', hComm, hAlg, hLocal, hLocalHom, hflat, hmax, hres, ?_⟩
  obtain ⟨e⟩ := hres
  exact Infinite.of_injective e.symm e.symm.injective

private lemma span_right_eq_top_of_tensorMap_surjective
    {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (f g : A →ₐ[C] B)
    (hfg : Function.Surjective
      (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _))) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    Submodule.span A (Set.range g) = ⊤ := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let T : Submodule A B := Submodule.span A (Set.range g)
  have hmap (x : A ⊗[C] A) :
      Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) x ∈ T := by
    induction x using TensorProduct.induction_on with
    | zero => simp [T]
    | add x y hx hy =>
        rw [map_add]
        exact T.add_mem hx hy
    | tmul a a' =>
        rw [Algebra.TensorProduct.lift_tmul]
        show algebraMap A B a * g a' ∈ T
        have hg : g a' ∈ T := Submodule.subset_span ⟨a', rfl⟩
        simpa [Algebra.smul_def] using T.smul_mem a hg
  refine top_unique fun b _ ↦ ?_
  obtain ⟨x, rfl⟩ := hfg b
  exact hmap x

private lemma rankAtStalk_eq_of_moduleRankCover
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M r) (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = r := by
  classical
  rcases h with ⟨ι, f, hfspan, hfbasis⟩
  have hcover : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ :=
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff).2 hfspan
  have hp : p ∈ (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) := by
    rw [hcover]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hp
  obtain ⟨i, hi⟩ := hp
  obtain ⟨b⟩ := hfbasis i
  have hfi : f i ∉ p.asIdeal := by
    simpa only [PrimeSpectrum.mem_basicOpen] using hi
  let S' := Submonoid.powers (f i)
  let R' := Localization S'
  let M' := LocalizedModule S' M
  let P' := Algebra.algebraMapSubmonoid R' p.asIdeal.primeCompl
  have hP' : S' ≤ p.asIdeal.primeCompl := by
    simpa [S', Submonoid.powers_le, Ideal.primeCompl] using hfi
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  have : IsLocalization.AtPrime Rₚ p.asIdeal := inferInstance
  have : Nontrivial Rₚ := IsLocalization.AtPrime.nontrivial Rₚ p.asIdeal
  let : Algebra R' Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S' p.asIdeal.primeCompl hP'
  let : IsScalarTower R R' Rₚ := IsLocalization.localization_isScalarTower_of_submonoid_le ..
  let : Module R' Mₚ := Module.compHom Mₚ (algebraMap R' Rₚ)
  let : IsScalarTower R R' Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  let : IsScalarTower R' Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • r' • m by
      rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := LinearMap.extendScalarsOfIsLocalization S' R'
    (IsLocalizedModule.liftOfLE _ _ hP'
      (LocalizedModule.mkLinearMap S' M) (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))
  have : IsLocalization P' Rₚ :=
    IsLocalization.isLocalization_of_submonoid_le R' Rₚ S' p.asIdeal.primeCompl hP'
  have : IsLocalizedModule p.asIdeal.primeCompl (l.restrictScalars R) := by
    simpa [l, LinearMap.restrictScalars_extendScalarsOfIsLocalization] using
      (inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
        (IsLocalizedModule.liftOfLE S' p.asIdeal.primeCompl hP'
          (LocalizedModule.mkLinearMap S' M)
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))))
  have : IsLocalizedModule P' l := IsLocalizedModule.of_restrictScalars p.asIdeal.primeCompl ..
  let : Module.Free R' M' := Module.Free.of_basis b
  let : Nontrivial R' := nontrivial_of_ne (1 : R') 0 (by
    intro h
    have h' := congrArg (algebraMap R' Rₚ) h
    simp at h')
  let : StrongRankCondition R' := commRing_strongRankCondition R'
  show Module.finrank Rₚ Mₚ = r
  have hfinrank := Module.finrank_of_isLocalizedModule_of_free Rₚ P' l
  rw [hfinrank, Module.finrank_eq_card_basis b]
  simp

private lemma specMap_rankAtStalk_eq_of_ranked_finiteLocallyFree
    (R S : CommRingCat.{u}) (φ : R ⟶ S) (r : ℕ)
    [h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Spec.map φ) r]
    (p : PrimeSpectrum R) :
    letI := φ.hom.toAlgebra
    Module.rankAtStalk S p = r := by
  let : Algebra R S := φ.hom.toAlgebra
  exact rankAtStalk_eq_of_moduleRankCover
    (specMap_module_rank_of_ranked_finiteLocallyFree R S φ r) p

private lemma map_maximalIdeal_le_jacobson_of_local_integral
    {C A : Type u} [CommRing C] [CommRing A] [IsLocalRing C]
    (f : C →+* A) (hf : f.IsIntegral) :
    Ideal.map f (IsLocalRing.maximalIdeal C) ≤ Ring.jacobson A := by
  rw [← Ideal.jacobson_bot, Ideal.jacobson, le_sInf_iff]
  rintro P ⟨-, hP⟩
  rw [Ideal.map_le_iff_le_comap]
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf P)).ge

/-- If `B` is finite over `A` along `t`, both `t` and `s` are integral, and every maximal ideal
of `A` is the image under `s` of a prime of `B` lying over a fixed maximal ideal `p₀` along `t`,
then `A` has finitely many maximal ideals. -/
private lemma finite_maximalSpectrum_of_finite_target_and_transitive_orbits
    {A B : Type u} [CommRing A] [CommRing B]
    (t s : A →+* B)
    (hfinite : letI : Algebra A B := t.toAlgebra; Module.Finite A B)
    (htint : t.IsIntegral) (hsint : s.IsIntegral)
    (p₀ : MaximalSpectrum A)
    (horbit : ∀ p : MaximalSpectrum A, ∃ q : PrimeSpectrum B,
      PrimeSpectrum.comap t q = p₀.toPrimeSpectrum ∧
      PrimeSpectrum.comap s q = p.toPrimeSpectrum) :
    Finite (MaximalSpectrum A) := by
  let : Algebra A B := t.toAlgebra
  let : Module.Finite A B := hfinite
  let F : Set (PrimeSpectrum B) :=
    {q | PrimeSpectrum.comap t q = p₀.toPrimeSpectrum}
  have hF : F.Finite := by
    show (PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p₀.toPrimeSpectrum}).Finite
    exact Algebra.QuasiFinite.finite_comap_preimage_singleton p₀.toPrimeSpectrum
  let : Finite F := hF.to_subtype
  let f : F → MaximalSpectrum A := fun q => by
    have hqmax : q.1.asIdeal.IsMaximal := by
      have hqt : PrimeSpectrum.comap t q.1 = p₀.toPrimeSpectrum := q.2
      have hqtIdeal : Ideal.comap t q.1.asIdeal = p₀.asIdeal := by
        simpa only [PrimeSpectrum.comap_asIdeal, MaximalSpectrum.toPrimeSpectrum] using
          congrArg PrimeSpectrum.asIdeal hqt
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' t htint
      exact hqtIdeal ▸ p₀.isMaximal
    let : q.1.asIdeal.IsMaximal := hqmax
    exact ⟨(PrimeSpectrum.comap s q.1).asIdeal,
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' s hsint q.1.asIdeal⟩
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨q, hqt, hqs⟩ := horbit p
    exact ⟨⟨q, hqt⟩, MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal hqs)⟩
  exact Finite.of_surjective f hf

/-- A finite locally free morphism of schemes is finite and flat. -/
private lemma isFinite_and_flat_of_isFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFree f] : IsFinite f ∧ Flat f :=
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    f).mp inferInstance
  ⟨h.1, h.2.1⟩

private lemma objectsToInvariantSpectrum_eq_of_maximalSpectrum
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsLocalRing (invariantRing G)]
    (p q : MaximalSpectrum Γ(G.objects.left, ⊤)) :
    objectsToInvariantSpectrum G (G.objects.left.isoSpec.inv p.toPrimeSpectrum) =
      objectsToInvariantSpectrum G (G.objects.left.isoSpec.inv q.toPrimeSpectrum) := by
  have hf := AlgebraicGeometry.isIntegral_over_invariantRing G
  have hmax (p : MaximalSpectrum Γ(G.objects.left, ⊤)) :
      Ideal.comap (invariantRing G).subtype p.asIdeal =
        IsLocalRing.maximalIdeal (invariantRing G) := by
    let : p.asIdeal.IsMaximal := p.isMaximal
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hf p.asIdeal)
  have he (p : PrimeSpectrum Γ(G.objects.left, ⊤)) :
      G.objects.left.isoSpec.hom (G.objects.left.isoSpec.inv p) = p :=
    congrArg (fun k : Spec Γ(G.objects.left, ⊤) ⟶ Spec Γ(G.objects.left, ⊤) ↦ k p)
      G.objects.left.isoSpec.inv_hom_id
  show PrimeSpectrum.comap (invariantRing G).subtype
      (G.objects.left.isoSpec.hom (G.objects.left.isoSpec.inv p.toPrimeSpectrum)) =
    PrimeSpectrum.comap (invariantRing G).subtype
      (G.objects.left.isoSpec.hom (G.objects.left.isoSpec.inv q.toPrimeSpectrum))
  rw [he, he]
  exact PrimeSpectrum.ext ((hmax p).trans (hmax q).symm)

/-- Over a local invariant ring, the object ring of a finite locally free equivalence relation
on an affine scheme has finitely many maximal ideals. -/
private lemma objectRing_finite_maximalSpectrum_of_local_invariants
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    [IsLocalRing (invariantRing G)] :
    Finite (MaximalSpectrum Γ(G.objects.left, ⊤)) := by
  classical
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let C := invariantRing G
  let t := targetMap G
  let s := sourceMap G
  have hiso (p : PrimeSpectrum A) :
      G.objects.left.isoSpec.hom (G.objects.left.isoSpec.inv p) = p :=
    congrArg (fun k : Spec A ⟶ Spec A ↦ k p) G.objects.left.isoSpec.inv_hom_id
  by_cases hC : Subsingleton C
  · have hA : Subsingleton A := by
      have h01c : (1 : C) = 0 := hC.elim _ _
      have h01 : (1 : A) = 0 := congrArg Subtype.val h01c
      exact subsingleton_of_zero_eq_one h01.symm
    let : Subsingleton A := hA
    let : IsEmpty (MaximalSpectrum A) := ⟨fun p => p.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    exact inferInstance
  · let : Nontrivial C := not_subsingleton_iff_nontrivial.mp hC
    let f : C →+* A := Subring.subtype C
    have hfint : f.IsIntegral := AlgebraicGeometry.isIntegral_over_invariantRing G
    obtain ⟨q₀, hq₀⟩ := hfint.comap_surjective Subtype.val_injective
      (⟨IsLocalRing.maximalIdeal C, IsLocalRing.maximalIdeal.isMaximal C⟩ :
        MaximalSpectrum C).toPrimeSpectrum
    have hq₀max : q₀.asIdeal.IsMaximal := by
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hfint q₀.asIdeal
      have he : Ideal.comap f q₀.asIdeal = IsLocalRing.maximalIdeal C :=
        congrArg PrimeSpectrum.asIdeal hq₀
      rw [he]
      infer_instance
    let p₀ : MaximalSpectrum A := ⟨q₀.asIdeal, hq₀max⟩
    have htfinite : let := t.toAlgebra; Module.Finite A B := by
      let : IsFinite G.target.left := (isFinite_and_flat_of_isFiniteLocallyFree G.target.left).1
      let : Algebra A B := t.toAlgebra
      show Module.Finite A B
      exact G.target.left.finite_appTop
    let : Algebra A B := t.toAlgebra
    let : Module.Finite A B := htfinite
    have htint : t.IsIntegral := RingHom.IsIntegral.of_finite htfinite
    have hsfinite : let := s.toAlgebra; Module.Finite A B := by
      let : IsFinite G.source.left := (isFinite_and_flat_of_isFiniteLocallyFree G.source.left).1
      let : Algebra A B := s.toAlgebra
      show Module.Finite A B
      exact G.source.left.finite_appTop
    have hsint : s.IsIntegral := RingHom.IsIntegral.of_finite hsfinite
    have horbit (p : MaximalSpectrum A) :
        ∃ q : PrimeSpectrum B,
          PrimeSpectrum.comap t q = p₀.toPrimeSpectrum ∧
          PrimeSpectrum.comap s q = p.toPrimeSpectrum := by
      let x₀ : G.objects.left := G.objects.left.isoSpec.inv.base p₀.toPrimeSpectrum
      let x : G.objects.left := G.objects.left.isoSpec.inv.base p.toPrimeSpectrum
      obtain ⟨a, htarget, hsource⟩ :=
        (AlgebraicGeometry.GroupoidScheme.base_objectsToInvariantSpectrum_eq_iff G x₀ x).mp
          (objectsToInvariantSpectrum_eq_of_maximalSpectrum G p₀ p)
      have hnat (f : G.arrows.left ⟶ G.objects.left) (y : PrimeSpectrum A)
          (h : f a = G.objects.left.isoSpec.inv.base y) :
          (Spec.map f.appTop) (G.arrows.left.isoSpec.hom a) = y := by
        have hn := congrArg (fun k : G.arrows.left ⟶ Spec A ↦ k a)
          (Scheme.toSpecΓ_naturality f)
        simpa only [Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom, h, hiso] using hn.symm
      exact ⟨G.arrows.left.isoSpec.hom.base a, hnat _ _ htarget, hnat _ _ hsource⟩
    exact finite_maximalSpectrum_of_finite_target_and_transitive_orbits
      t s htfinite htint hsint p₀ horbit

lemma arrows_hom_ext {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] {T : Scheme.{u}}
    (f g : T ⟶ G.arrows.left)
    (ht : f ≫ G.target.left = g ≫ G.target.left)
    (hs : f ≫ G.source.left = g ≫ G.source.left) : f = g := by
  let T' := Over.mk (f ≫ G.arrows.hom)
  let f' : T' ⟶ G.arrows := Over.homMk f
  let g' : T' ⟶ G.arrows := Over.homMk g (by
    show g ≫ G.arrows.hom = f ≫ G.arrows.hom
    rw [← Over.w G.source, ← Category.assoc, ← hs, Category.assoc])
  let e : EquivalenceRelation G.target G.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  exact congrArg (fun k : T' ⟶ G.arrows ↦ k.left)
    (e.right_cancellation f' g' (Over.OverMorphism.ext ht) (Over.OverMorphism.ext hs))

lemma tensorMap_surjective {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left]
    [IsEquivalenceRelation G.target G.source] :
    letI := invariantRingAlgebraArrow G
    Function.Surjective (Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
      (fun _ _ ↦ Commute.all _ _)) := by
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let C := invariantRing G
  let := invariantRingAlgebraArrow G
  let φ := Algebra.TensorProduct.lift (sourceAlgHom G) (targetAlgHom G)
    (fun _ _ ↦ Commute.all _ _)
  let k := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let l := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[C] A))
  let r := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[C] A ⊗[C] A).toRingHom)
  have hl : k ≫ l = Spec.map G.source.left.appTop := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    show φ (a ⊗ₜ[C] 1) = sourceMap G a
    exact (Algebra.TensorProduct.lift_tmul (sourceAlgHom G) (targetAlgHom G)
      (fun _ _ ↦ Commute.all _ _) a 1).trans (by rw [map_one, mul_one]; rfl)
  have hr : k ≫ r = Spec.map G.target.left.appTop := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    show φ (1 ⊗ₜ[C] a) = targetMap G a
    exact (Algebra.TensorProduct.lift_tmul (sourceAlgHom G) (targetAlgHom G)
      (fun _ _ ↦ Commute.all _ _) 1 a).trans (by rw [map_one, one_mul]; rfl)
  have hi {u : Spec (.of (A ⊗[C] A)) ⟶ Spec (.of A)} {f : G.arrows.left ⟶ G.objects.left}
      (hu : k ≫ u = Spec.map f.appTop) :
      k ≫ u ≫ G.objects.left.isoSpec.inv = G.arrows.left.isoSpec.inv ≫ f := by
    have h : G.arrows.left.isoSpec.hom ≫ k ≫ u = f ≫ G.objects.left.isoSpec.hom := by
      rw [hu]
      exact (Scheme.toSpecΓ_naturality f).symm
    rw [← cancel_epi G.arrows.left.isoSpec.hom]
    simp only [Iso.hom_inv_id_assoc]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun a ↦ a ≫ G.objects.left.isoSpec.inv) h
  have hsi := hi hl
  have hti := hi hr
  let : Mono k := ⟨fun f g h ↦ by
    apply (cancel_mono G.arrows.left.isoSpec.inv).1
    apply arrows_hom_ext G
    · simpa only [Category.assoc, ← hti] using
        congrArg (fun a ↦ a ≫ r ≫ G.objects.left.isoSpec.inv) h
    · simpa only [Category.assoc, ← hsi] using
        congrArg (fun a ↦ a ≫ l ≫ G.objects.left.isoSpec.inv) h⟩
  let : IsFinite G.source.left := (isFinite_and_flat_of_isFiniteLocallyFree G.source.left).1
  let : IsFinite (k ≫ l) := by
    rw [hl, IsFinite.SpecMap_iff]
    exact G.source.left.finite_appTop
  let : IsFinite k := IsFinite.of_comp k l
  let : IsClosedImmersion k := (IsClosedImmersion.iff_isFinite_and_mono k).mpr
    ⟨inferInstance, inferInstance⟩
  have hk := (IsClosedImmersion.isAffine_surjective_of_isAffine k).2
  have hφ := (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.surjective.comp hk
  intro b
  obtain ⟨a, ha⟩ := hφ b
  refine ⟨(Scheme.ΓSpecIso (.of (A ⊗[C] A))).hom a, ?_⟩
  change (k.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom) a = b at ha
  rw [Scheme.ΓSpecIso_naturality] at ha
  exact ha

private lemma isPullback_comp_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] :
    IsPullback G.comp (pullback.snd G.source G.target) G.source G.source := by
  let e : EquivalenceRelation G.target G.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  let first (c : PullbackCone G.source G.source) : c.pt ⟶ G.arrows :=
    G.compose c.fst (c.snd ≫ G.inverse) (by
      simpa only [Category.assoc, G.target_inverse] using c.condition)
  have first_source (c : PullbackCone G.source G.source) :
      first c ≫ G.source = c.snd ≫ G.target := by
    simp only [first, GroupoidScheme.compose, Category.assoc, G.source_comp,
      pullback.lift_snd_assoc, G.source_inverse]
  have first_target (c : PullbackCone G.source G.source) :
      first c ≫ G.target = c.fst ≫ G.target := by
    simp only [first, GroupoidScheme.compose, Category.assoc, G.target_comp,
      pullback.lift_fst_assoc]
  let lift (c : PullbackCone G.source G.source) :=
    pullback.lift (first c) c.snd (first_source c)
  have fac (c : PullbackCone G.source G.source) : lift c ≫ G.comp = c.fst := by
    apply e.right_cancellation
    · simp only [Category.assoc, G.target_comp, lift, pullback.lift_fst_assoc, first_target]
    · simp only [Category.assoc, G.source_comp, lift, pullback.lift_snd_assoc]
      exact c.condition.symm
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk G.source_comp lift fac
    (fun c ↦ pullback.lift_snd _ _ _) ?_)
  intro c m hm hn
  apply pullback.hom_ext
  · dsimp only [lift]
    rw [pullback.lift_fst]
    apply e.right_cancellation
    · rw [first_target, Category.assoc, ← G.target_comp, ← Category.assoc, hm]
    · rw [first_source, Category.assoc, pullback.condition, ← Category.assoc, hn]
  · simpa only [lift, pullback.lift_snd] using hn

private lemma source_finrank_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left]
    [IsEquivalenceRelation G.target G.source] (r : G.arrows.left) :
    G.source.left.finrank (G.source.left r) =
      G.source.left.finrank (G.target.left r) := by
  have h := isFinite_and_flat_of_isFiniteLocallyFree G.source.left
  let : IsFinite G.source.left := h.1
  let : Flat G.source.left := h.2
  have h₁ : IsPullback G.comp.left (pullback.snd G.source G.target).left
      G.source.left G.source.left := (isPullback_comp_snd G).map (Over.forget S)
  have h₂ : IsPullback (pullback.fst G.source G.target).left
      (pullback.snd G.source G.target).left G.source.left G.target.left :=
    (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ h₁ r).symm.trans
    (Scheme.Hom.finrank_of_isPullback _ _ _ _ h₂ r)

private lemma finrank_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Flat f] [IsFinite f] (p : PrimeSpectrum Γ(Y, ⊤)) :
    f.appTop.hom.finrank p = f.finrank (Y.isoSpec.inv p) := by
  have hpb : IsPullback X.isoSpec.inv (Spec.map f.appTop) f Y.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by
      rw [← cancel_epi X.isoSpec.hom]
      simp only [Iso.hom_inv_id_assoc]
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun k ↦ k ≫ Y.isoSpec.inv) (Scheme.isoSpec_hom_naturality f).symm⟩
  rw [← Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop]
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb p

private lemma finrank_quotient_tensor_eq_rankAtStalk
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : MaximalSpectrum R) :
    Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      Module.rankAtStalk M P.toPrimeSpectrum := by
  let : P.asIdeal.IsMaximal := P.isMaximal
  let : Field (R ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let q : PrimeSpectrum (R ⧸ P.asIdeal) := ⟨⊥, inferInstance⟩
  have hq : PrimeSpectrum.comap (algebraMap R (R ⧸ P.asIdeal)) q =
      P.toPrimeSpectrum :=
    PrimeSpectrum.ext (Ideal.ext fun _ ↦ Ideal.Quotient.eq_zero_iff_mem)
  have h := Module.rankAtStalk_baseChange (R := R) (M := M) q
  rwa [Module.rankAtStalk_eq_finrank_of_free, hq] at h

lemma exists_basis_and_tensorEquiv_of_local_invariants
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    [IsLocalRing (invariantRing G)]
    [Infinite (IsLocalRing.ResidueField (invariantRing G))] :
    ∃ n, ∃ _b : Module.Basis (Fin n) (invariantRing G) Γ(G.objects.left, ⊤),
      ∃ e : RingEquiv (Γ(G.objects.left, ⊤) ⊗[invariantRing G] Γ(G.objects.left, ⊤))
          Γ(G.arrows.left, ⊤),
        ∀ a a', e (a ⊗ₜ[invariantRing G] a') = sourceMap G a * targetMap G a' := by
  classical
  let A := Γ(G.objects.left, ⊤)
  let B := Γ(G.arrows.left, ⊤)
  let C := invariantRing G
  let : Algebra A B := (sourceMap G).toAlgebra
  have hs := isFinite_and_flat_of_isFiniteLocallyFree G.source.left
  let : IsFinite G.source.left := hs.1
  let : Flat G.source.left := hs.2
  have hfinite : Module.Finite A B := G.source.left.finite_appTop
  have hflat : Module.Flat A B := G.source.left.flat_appTop
  let : Module.Finite A B := hfinite
  let : Module.Flat A B := hflat
  have hrank : ∃ r, ∀ P : MaximalSpectrum A,
      Module.finrank (A ⧸ P.asIdeal) ((A ⧸ P.asIdeal) ⊗[A] B) = r := by
    by_cases hn : Nonempty (MaximalSpectrum A)
    · obtain ⟨P₀⟩ := hn
      refine ⟨G.source.left.finrank (G.objects.left.isoSpec.inv P₀.toPrimeSpectrum), ?_⟩
      intro P
      rw [finrank_quotient_tensor_eq_rankAtStalk]
      show G.source.left.appTop.hom.finrank P.toPrimeSpectrum = _
      apply (finrank_appTop G.source.left P.toPrimeSpectrum).trans
      have hq := objectsToInvariantSpectrum_eq_of_maximalSpectrum G P P₀
      obtain ⟨a, ht, hs⟩ :=
        (AlgebraicGeometry.GroupoidScheme.base_objectsToInvariantSpectrum_eq_iff G _ _).mp hq
      rw [← ht, ← hs]
      exact (source_finrank_eq G a).symm
    · exact ⟨0, fun P ↦ (hn ⟨P⟩).elim⟩
  obtain ⟨r, hrank⟩ := hrank
  have hspan : Submodule.span A (Set.range (targetMap G)) = ⊤ :=
    span_right_eq_top_of_tensorMap_surjective (sourceAlgHom G) (targetAlgHom G)
      (tensorMap_surjective G)
  exact tensorProduct_equiv_arrowRing_of_semilocal_basis G
    (objectRing_finite_maximalSpectrum_of_local_invariants G)
    (map_maximalIdeal_le_jacobson_of_local_integral C.subtype
      (AlgebraicGeometry.isIntegral_over_invariantRing G)) hfinite hflat hrank hspan

end AlgebraicGeometry

end

end
