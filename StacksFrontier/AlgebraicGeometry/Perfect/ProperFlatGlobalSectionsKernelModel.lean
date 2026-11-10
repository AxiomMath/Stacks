module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsFunctorialModel
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
public import StacksFrontier.Homology.Perfect.Saturation

/-!
# Global sections of base changes as the kernel of one matrix

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism and `F` a coherent `𝒪_X`-module
flat over `A`, and let `p` be a prime of `A`. This file proves that near `p` the global sections
of every base change of `F` are the kernel of a single matrix over `A` whose entries lie in `p`,
naturally in the base change. This is the degree-`0` local model used in the proof of
[Stacks, Tag 0BDL].

## Main definitions

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.kernelChainComparison`: for a chain-level
  model `u : P ⟶ Č ⊗_A R` of the `A`-linear Čech model over an `A`-algebra `R`, the chain map
  `P ⊗_R B ⟶ Č(X', F')` for every `R`-algebra `B` and every base change `X'` of `X` to `B`.
* `…kernelModelEquiv`: when `P` vanishes in degree `-1` and its first differential is the
  matrix `M`, the identification `ker(M ⊗ B) ≃ Γ(X', F')`.

## Main results

* `…quasiIso_kernelChainComparison` and `…kernelChainComparison_comp`: the chain-level
  comparison is a quasi-isomorphism and satisfies the cocycle square for a second base change;
  the latter is `baseAlternatingCechComplexBaseChangeIso_comp` together with the associativity
  of `ModuleCat.extendScalarsComp`.
* `…kernelModelEquiv_comp`: the identification `ker(M ⊗ B) ≃ Γ(X', F')` is natural in `B`.
* `…matrix_map_eq_zero_of_finrank`: minimality — if over a residue field the degree-`0`
  homology has the rank of the degree-`0` term, the matrix vanishes there.
* `…exists_away_kernelModel`: the main theorem.

## Implementation notes

The model `P` is the minimal representative of [Stacks, Tag 0BYP] (and [Stacks, Tag 0BCD]) of
the derived base change to `A_g` of the Čech model `Č` of a finite affine cover with affine
intersections: it lives in degrees `≥ 0` and its term in degree `i` is free of rank
`dim Hⁱ(Č ⊗ᴸ κ(p))`. Being K-projective, `P` maps to `Č ⊗_A A_g` by a chain map inducing that
identification. The ranks force the differential `P⁰ → P¹` to vanish modulo `p`; clearing
denominators gives the matrix `D` over `A`, and `D ⊗ B` is `M ⊗ B` up to the unit `g^N`.

Degree-`0` homology is never formed: a quasi-isomorphism between complexes vanishing in degree
`-1` is bijective on the kernels of the differentials out of degree `0`
(`bijective_kerRestrict`), and the kernel of the first Čech differential is the module of global
sections (`range_sectionsToModel`). The `B`-module structure on `Γ(X', F')` is
`Stacks.Cech.sectionsModule`.

The comparisons are composed with `Eq.trans` chains rather than rewriting, because their goals mix
definitionally but not reducibly equal spellings of the terms of termwise functor images.

The file runs under `HasDerivedCategory.standard` at priority `10000`, as the files it builds on.

## References

* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
* [Stacks Project, Tag 0BYP](https://stacks.math.columbia.edu/tag/0BYP)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section Algebra

/-- The associativity of `ModuleCat.extendScalarsComp`, read on the inverses at a module. -/
theorem extendScalarsComp_inv_app_assoc {A₁ A₂ A₃ A₄ : Type u} [CommRing A₁]
    [CommRing A₂] [CommRing A₃] [CommRing A₄] (f₁ : A₁ →+* A₂) (f₂ : A₂ →+* A₃) (f₃ : A₃ →+* A₄)
    (N : ModuleCat.{u} A₁) :
    (ModuleCat.extendScalarsComp f₂ f₃).inv.app ((ModuleCat.extendScalars.{u, u, u} f₁).obj N) ≫
        (ModuleCat.extendScalarsComp f₁ (f₃.comp f₂)).inv.app N =
      (ModuleCat.extendScalars.{u, u, u} f₃).map ((ModuleCat.extendScalarsComp f₁ f₂).inv.app N) ≫
        (ModuleCat.extendScalarsComp (f₂.comp f₁) f₃).inv.app N := by
  have h := congr_app (ModuleCat.extendScalars_assoc f₁ f₂ f₃) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id] at h
  have e1 : (ModuleCat.extendScalarsComp f₂ f₃).inv.app
        ((ModuleCat.extendScalars.{u, u, u} f₁).obj N) ≫
        (ModuleCat.extendScalarsComp f₁ (f₃.comp f₂)).inv.app N =
      inv ((ModuleCat.extendScalarsComp f₁ (f₃.comp f₂)).hom.app N ≫
        (ModuleCat.extendScalarsComp f₂ f₃).hom.app
          ((ModuleCat.extendScalars.{u, u, u} f₁).obj N)) := by
    simp
  have e2 : (ModuleCat.extendScalars.{u, u, u} f₃).map
        ((ModuleCat.extendScalarsComp f₁ f₂).inv.app N) ≫
        (ModuleCat.extendScalarsComp (f₂.comp f₁) f₃).inv.app N =
      inv ((ModuleCat.extendScalarsComp (f₂.comp f₁) f₃).hom.app N ≫
        (ModuleCat.extendScalars.{u, u, u} f₃).map
          ((ModuleCat.extendScalarsComp f₁ f₂).hom.app N)) := by
    simp [← Functor.map_inv]
  rw [e1, e2]
  simp only [h]

/-- A morphism of short complexes of modules maps the kernel of the second map into the kernel
of the second map. -/
theorem map_mem_ker_g {R : Type u} [CommRing R] {S₁ S₂ : ShortComplex (ModuleCat.{u} R)}
    (φ : S₁ ⟶ S₂) (x : S₁.X₂) (hx : x ∈ LinearMap.ker S₁.g.hom) :
    φ.τ₂.hom x ∈ LinearMap.ker S₂.g.hom := by
  rw [LinearMap.mem_ker] at hx ⊢
  have h := congr($(φ.comm₂₃).hom x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, hx, map_zero]

/-- **A quasi-isomorphism of short complexes of modules with vanishing first maps is bijective
on the kernels of the second maps.** -/
theorem bijective_restrict_of_quasiIso {R : Type u} [CommRing R]
    {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂) [ShortComplex.QuasiIso φ]
    (hf₁ : S₁.f = 0) (hf₂ : S₂.f = 0) :
    Function.Bijective (φ.τ₂.hom.restrict (p := LinearMap.ker S₁.g.hom)
      (q := LinearMap.ker S₂.g.hom) (map_mem_ker_g φ)) := by
  have h1 := S₁.isIso_homologyπ hf₁
  have h2 := S₂.isIso_homologyπ hf₂
  have hc : IsIso (ShortComplex.cyclesMap φ) := by
    have e : ShortComplex.cyclesMap φ =
        S₁.homologyπ ≫ ShortComplex.homologyMap φ ≫ inv S₂.homologyπ := by
      rw [ShortComplex.homologyπ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  let E := (S₁.moduleCatCyclesIso.symm ≪≫ asIso (ShortComplex.cyclesMap φ) ≪≫
    S₂.moduleCatCyclesIso).toLinearEquiv
  have hE : ∀ x, φ.τ₂.hom.restrict (p := LinearMap.ker S₁.g.hom)
      (q := LinearMap.ker S₂.g.hom) (map_mem_ker_g φ) x = E x := fun x => by
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply]
    have a1 := congr($(S₂.moduleCatCyclesIso_hom_i).hom
      (ShortComplex.cyclesMap φ (S₁.moduleCatCyclesIso.inv x)))
    have a2 := congr($(ShortComplex.cyclesMap_i φ).hom (S₁.moduleCatCyclesIso.inv x))
    have a3 := congr($(S₁.moduleCatCyclesIso_inv_iCycles).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at a1 a2 a3
    exact (congrArg φ.τ₂.hom a3.symm).trans (a2.symm.trans a1.symm)
  have : (φ.τ₂.hom.restrict (p := LinearMap.ker S₁.g.hom) (q := LinearMap.ker S₂.g.hom)
      (map_mem_ker_g φ) : _ → _) = E := funext hE
  rw [this]
  exact E.bijective

/-- The restriction of the degree-`0` component of a morphism of cochain complexes to the kernels
of the differentials out of degree `0`. -/
def kerRestrict {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (T : K ⟶ L) : LinearMap.ker (K.d 0 1).hom →ₗ[R] LinearMap.ker (L.d 0 1).hom :=
  (T.f 0).hom.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    have h := congr($(T.comm 0 1).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hx, map_zero]

/-- The restriction of a morphism to the cocycles is the degree-`0` component. -/
@[simp]
theorem kerRestrict_apply_coe {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (T : K ⟶ L) (x : LinearMap.ker (K.d 0 1).hom) :
    (kerRestrict T x : L.X 0) = T.f 0 x := rfl

/-- **A morphism of cochain complexes of modules which is a quasi-isomorphism in degree `0`,
between complexes whose differentials into degree `0` vanish, is bijective on the kernels of the
differentials out of degree `0`.** -/
theorem bijective_kerRestrict {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (T : K ⟶ L) [QuasiIsoAt T 0] (hK : K.d (-1) 0 = 0) (hL : L.d (-1) 0 = 0) :
    Function.Bijective (kerRestrict T) := by
  have hq := (quasiIsoAt_iff' T (-1) 0 1 (by simp) (by simp)).1 inferInstance
  exact bijective_restrict_of_quasiIso
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-1) 0 1).map T)
    hK hL

/-- The degree-`0` homology of a cochain complex of modules whose differential into degree `0`
vanishes is the kernel of the differential out of degree `0`. -/
def homologyZeroIsoKer {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.d (-1) 0 = 0) :
    K.homology 0 ≅ ModuleCat.of R (LinearMap.ker (K.d 0 1).hom) :=
  K.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    (@asIso _ _ _ _ _ ((K.sc' (-1) 0 1).isIso_homologyπ hK)).symm ≪≫
    (K.sc' (-1) 0 1).moduleCatCyclesIso

end Algebra

section TermEquiv

open scoped ChangeOfRings TensorProduct Matrix

variable {R B : Type u} [CommRing R] [CommRing B] (ψ : R →+* B) {r : ℕ}

/-- Extension of scalars of a module identified with `R^r` is identified with `B^r`. -/
def termEquiv {N : ModuleCat.{u} R} (e : N ≅ ModuleCat.of R (Fin r → R)) :
    (ModuleCat.extendScalars.{u, u, u} ψ).obj N ≃ₗ[B] (Fin r → B) :=
  ((ModuleCat.extendScalars.{u, u, u} ψ).mapIso e).toLinearEquiv ≪≫ₗ
    Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv ψ r

/-- The identification `termEquiv` on a pure tensor. -/
theorem termEquiv_tmul {N : ModuleCat.{u} R} (e : N ≅ ModuleCat.of R (Fin r → R)) (b : B)
    (x : N) : termEquiv ψ e (b ⊗ₜ[R, ψ] x) = fun k => ψ (e.hom x k) * b := by
  let := ψ.toAlgebra
  exact Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv_tmul ψ r b (e.hom x)

/-- Under `termEquiv`, the extension of scalars of a map with matrix `M` is multiplication by
`M.map ψ`. -/
theorem termEquiv_map {β : ℕ} {N N' : ModuleCat.{u} R} (e : N ≅ ModuleCat.of R (Fin r → R))
    (e' : N' ≅ ModuleCat.of R (Fin β → R)) (d : N ⟶ N') (M : Matrix (Fin β) (Fin r) R)
    (hM : d = e.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e'.inv)
    (x : (ModuleCat.extendScalars.{u, u, u} ψ).obj N) :
    termEquiv ψ e' ((ModuleCat.extendScalars.{u, u, u} ψ).map d x) =
      M.map ψ *ᵥ termEquiv ψ e x := by
  subst hM
  have h := Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv_naturality ψ M
    ((ModuleCat.extendScalars.{u, u, u} ψ).map e.hom x)
  refine Eq.trans ?_ h
  change Stacks.Eta.DeterminantalIdeal.baseChangeTermEquiv ψ β
      ((ModuleCat.extendScalars.{u, u, u} ψ).map e'.hom
        ((ModuleCat.extendScalars.{u, u, u} ψ).map (e.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e'.inv)
          x)) = _
  congr 1
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp,
    CategoryTheory.comp_apply]

/-- `termEquiv` is compatible with the composition isomorphism of extensions of scalars. -/
theorem termEquiv_comp_inv_app {B' : Type u} [CommRing B'] (ψ' : B →+* B') {N : ModuleCat.{u} R}
    (e : N ≅ ModuleCat.of R (Fin r → R))
    (y : (ModuleCat.extendScalars.{u, u, u} ψ').obj ((ModuleCat.extendScalars.{u, u, u} ψ).obj N)) :
    termEquiv (ψ'.comp ψ) e ((ModuleCat.extendScalarsComp ψ ψ').inv.app N y) =
      termEquiv ψ' (termEquiv ψ e).toModuleIso y := by
  have h : (ModuleCat.extendScalarsComp ψ ψ').inv.app N ≫
      (termEquiv (ψ'.comp ψ) e).toModuleIso.hom =
        (termEquiv ψ' (termEquiv ψ e).toModuleIso).toModuleIso.hom := by
    refine Stacks.Cech.extendScalars_hom_ext_one_one_tmul ψ ψ' fun s => ?_
    refine (CategoryTheory.comp_apply _ _ _).trans ?_
    refine (congrArg (termEquiv (ψ'.comp ψ) e)
      (Stacks.Cech.extendScalarsComp_inv_app_one_one_tmul ψ ψ' N s)).trans ?_
    refine (termEquiv_tmul (ψ'.comp ψ) e 1 s).trans ?_
    refine Eq.trans ?_ (termEquiv_tmul ψ' (termEquiv ψ e).toModuleIso 1 _).symm
    funext k
    change ψ' (ψ (e.hom s k)) * 1 = ψ' (termEquiv ψ e ((1 : B) ⊗ₜ[R, ψ] s) k) * 1
    rw [termEquiv_tmul ψ e 1 s]
    simp
  exact congr($(h).hom y)

/-- `termEquiv` carries `1 ⊗ x` over the composite ring map to the image of the coordinates of
`x`. -/
theorem termEquiv_comp {B' : Type u} [CommRing B'] (ψ' : B →+* B') {N : ModuleCat.{u} R}
    (e : N ≅ ModuleCat.of R (Fin r → R)) (x : (ModuleCat.extendScalars.{u, u, u} ψ).obj N) :
    termEquiv (ψ'.comp ψ) e ((ModuleCat.extendScalarsComp ψ ψ').inv.app N ((1 : B') ⊗ₜ[B, ψ'] x)) =
      ψ' ∘ termEquiv ψ e x := by
  refine (termEquiv_comp_inv_app ψ ψ' e _).trans ?_
  refine (termEquiv_tmul ψ' (termEquiv ψ e).toModuleIso 1 x).trans ?_
  funext k
  change ψ' (termEquiv ψ e x k) * 1 = _
  simp

end TermEquiv

section DegreeZero

/-- A diagrammatic step: a commuting square followed by isomorphisms which pin the second
differential. -/
theorem comp_eq_of_square {C : Type*} [Category C] {P₀ P₁ E₀ E₁ Y₀ Y₁ : C}
    (dP : P₀ ⟶ P₁) (ι₀ : P₀ ⟶ E₀) (ι₁ : P₁ ⟶ E₁) (dE : E₀ ⟶ E₁)
    (hcomm : ι₀ ≫ dE = dP ≫ ι₁) (x₀ : E₀ ≅ Y₀) (x₁ : E₁ ≅ Y₁) (dY : Y₀ ⟶ Y₁)
    (hdE : dE = x₀.hom ≫ dY ≫ x₁.inv) {X₀ : P₀ ⟶ Y₀} {X₁ : P₁ ⟶ Y₁} {dY' : Y₀ ⟶ Y₁}
    (h₀ : ι₀ ≫ x₀.hom = X₀) (h₁ : ι₁ ≫ x₁.hom = X₁) (hd : dY = dY') :
    dP ≫ X₁ = X₀ ≫ dY' := by
  subst h₀ h₁ hd hdE
  rw [← Category.assoc, ← hcomm]
  simp

variable {B : Type u} [CommRing B] {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of B)) {I : Type u}
  (U' : I → X'.Opens) (hU' : (⊤ : X'.Opens) = ⨆ i, U' i) (F' : X'.Modules)

/-- The differential of the `ℤ`-indexed Čech model out of degree `0` is the alternating Čech
differential out of degree `0`. -/
theorem baseAlternatingCechComplex_d_zero_one :
    (baseAlternatingCechComplex f' U' hU' F').d ((0 : ℕ) : ℤ) ((1 : ℕ) : ℤ) ≫
        (baseAlternatingCechComplexXIso f' U' hU' F' 1).hom =
      (baseAlternatingCechComplexXIso f' U' hU' F' 0).hom ≫
        Stacks.Cech.alternatingCechModuleDiff f' U' F' 0 :=
  comp_eq_of_square _ _ _ _ ((baseAlternatingCechComplexIsoExtend f' U' hU' F').hom.comm _ _)
    _ _ _ (HomologicalComplex.extend_d_eq _ _ (ComplexShape.embeddingUpNat_f 0)
      (ComplexShape.embeddingUpNat_f 1))
    (baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f' U' hU' F' 0)
    (baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f' U' hU' F' 1)
    (Stacks.Cech.alternatingCechModuleComplex_d f' U' F' 0)

/-- Global sections of `F'` as degree-`0` cochains of the `ℤ`-indexed Čech model. -/
def sectionsToModel :
    letI := Stacks.Cech.sectionsModule f' F' ⊤
    Γ(F', ⊤) →ₗ[B] (baseAlternatingCechComplex f' U' hU' F').X 0 :=
  letI := Stacks.Cech.sectionsModule f' F' ⊤
  letI := Stacks.Cech.cochainModule f' U' F' 0
  (baseAlternatingCechComplexXIso f' U' hU' F' 0).inv.hom ∘ₗ
    Stacks.Cech.sectionsToAlternatingₗ f' U' F' (fun _ => le_top)

/-- Read in the alternating Čech cochains, the cochain of a section is its family of
restrictions. -/
theorem baseAlternatingCechComplexXIso_hom_sectionsToModel (s : Γ(F', ⊤)) :
    (baseAlternatingCechComplexXIso f' U' hU' F' 0).hom (sectionsToModel f' U' hU' F' s) =
      Stacks.Cech.sectionsToAlternatingₗ f' U' F' (fun _ => le_top) s := by
  change ((baseAlternatingCechComplexXIso f' U' hU' F' 0).inv ≫
    (baseAlternatingCechComplexXIso f' U' hU' F' 0).hom) _ = _
  rw [Iso.inv_hom_id]
  rfl

/-- A global section is determined by its degree-`0` Čech cochain. -/
theorem sectionsToModel_injective : Function.Injective (sectionsToModel f' U' hU' F') := by
  intro s t h
  have h' := congrArg (baseAlternatingCechComplexXIso f' U' hU' F' 0).hom h
  rw [baseAlternatingCechComplexXIso_hom_sectionsToModel,
    baseAlternatingCechComplexXIso_hom_sectionsToModel] at h'
  exact Stacks.Cech.sectionsToAlternatingₗ_injective f' U' F' (fun _ => le_top) hU'.le h'

/-- The degree-`0` cochains of global sections are exactly the degree-`0` cocycles of the
`ℤ`-indexed Čech model. -/
theorem range_sectionsToModel :
    letI := Stacks.Cech.sectionsModule f' F' ⊤
    LinearMap.range (sectionsToModel f' U' hU' F') =
      LinearMap.ker ((baseAlternatingCechComplex f' U' hU' F').d 0 1).hom := by
  let := Stacks.Cech.sectionsModule f' F' ⊤
  let := Stacks.Cech.cochainModule f' U' F' 0
  let := Stacks.Cech.cochainModule f' U' F' 1
  have hd := baseAlternatingCechComplex_d_zero_one f' U' hU' F'
  have hr := Stacks.Cech.range_sectionsToAlternatingₗ f' U' F' (fun _ => le_top) hU'.le
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    rw [LinearMap.mem_ker]
    apply (baseAlternatingCechComplexXIso f' U' hU' F' 1).toLinearEquiv.injective
    have := congr($(hd).hom (sectionsToModel f' U' hU' F' s))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    refine this.trans ?_
    rw [map_zero]
    change Stacks.Cech.alternatingCechModuleD f' U' F' 0
      ((baseAlternatingCechComplexXIso f' U' hU' F' 0).hom (sectionsToModel f' U' hU' F' s)) = 0
    rw [baseAlternatingCechComplexXIso_hom_sectionsToModel, ← LinearMap.mem_ker, ← hr]
    exact ⟨s, rfl⟩
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have := congr($(hd).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    have hx' : (baseAlternatingCechComplexXIso f' U' hU' F' 0).hom x ∈
        LinearMap.ker (Stacks.Cech.alternatingCechModuleD f' U' F' 0) := by
      have h0 : (baseAlternatingCechComplexXIso f' U' hU' F' 1).hom.hom
          (((baseAlternatingCechComplex f' U' hU' F').d 0 1).hom x) = 0 := by
        rw [hx, map_zero]
      exact this.symm.trans h0
    obtain ⟨s, hs⟩ : (baseAlternatingCechComplexXIso f' U' hU' F' 0).hom x ∈
        LinearMap.range (Stacks.Cech.sectionsToAlternatingₗ f' U' F' (fun _ => le_top)) :=
      (SetLike.ext_iff.1 hr _).2 hx'
    exact ⟨s, (baseAlternatingCechComplexXIso f' U' hU' F' 0).toLinearEquiv.injective
      ((baseAlternatingCechComplexXIso_hom_sectionsToModel f' U' hU' F' s).trans hs)⟩

/-- **Global sections are the degree-`0` cocycles of the `ℤ`-indexed Čech model.** -/
def sectionsEquivKer :
    letI := Stacks.Cech.sectionsModule f' F' ⊤
    Γ(F', ⊤) ≃ₗ[B] LinearMap.ker ((baseAlternatingCechComplex f' U' hU' F').d 0 1).hom :=
  letI := Stacks.Cech.sectionsModule f' F' ⊤
  (LinearEquiv.ofInjective _ (sectionsToModel_injective f' U' hU' F')).trans
    (LinearEquiv.ofEq _ _ (range_sectionsToModel f' U' hU' F'))

/-- `sectionsEquivKer` is the cochain of a section. -/
theorem sectionsEquivKer_apply_coe (s : Γ(F', ⊤)) :
    (sectionsEquivKer f' U' hU' F' s : (baseAlternatingCechComplex f' U' hU' F').X 0) =
      sectionsToModel f' U' hU' F' s := rfl

/-- The degree-`0` cochain of a section is natural in the module. -/
theorem sectionsToModel_mapIso {G H : X'.Modules} (t : G ≅ H) (s : Γ(G, ⊤)) :
    (baseAlternatingCechComplexMapIso f' U' hU' t).hom.f 0 (sectionsToModel f' U' hU' G s) =
      sectionsToModel f' U' hU' H (t.hom.app ⊤ s) := by
  apply (baseAlternatingCechComplexXIso f' U' hU' H 0).toLinearEquiv.injective
  have h := congr($(baseAlternatingCechComplexMapIso_hom_f_comp_XIso f' U' hU' t 0).hom
    (sectionsToModel f' U' hU' G s))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine h.trans ?_
  change Stacks.Cech.alternatingCechModuleObjMap f' U' t.hom 0
      ((baseAlternatingCechComplexXIso f' U' hU' G 0).hom (sectionsToModel f' U' hU' G s)) =
    (baseAlternatingCechComplexXIso f' U' hU' H 0).hom (sectionsToModel f' U' hU' H _)
  rw [baseAlternatingCechComplexXIso_hom_sectionsToModel,
    baseAlternatingCechComplexXIso_hom_sectionsToModel]
  refine Subtype.ext (funext fun i => ?_)
  exact congr($(t.hom.mapPresheaf.naturality
    (homOfLE (Stacks.Cech.inter_le_of_le U' (fun _ => le_top) i)).op) s)

end DegreeZero

section SectionsBaseChange

open scoped ChangeOfRings TensorProduct

variable {B B' : Type u} [CommRing B] [CommRing B'] (ψ' : B →+* B') {X' X'' : Scheme.{u}}
  {f' : X' ⟶ Spec (.of B)} [IsSeparated f'] {f'' : X'' ⟶ Spec (.of B')} {g'' : X'' ⟶ X'}
  (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ'))) (F' : X'.Modules)
  [F'.IsQuasicoherent] {I : Type u} [Finite I] (U' : I → X'.Opens)
  (hU' : (⊤ : X'.Opens) = ⨆ i, U' i) (hU'aff : ∀ i, IsAffineOpen (U' i))

/-- **The Čech base-change isomorphism carries the cochain of a section to the cochain of its
pullback.** -/
theorem baseChangeIso_sectionsToModel (s : Γ(F', ⊤)) :
    (baseAlternatingCechComplexBaseChangeIso ψ' hsq' F' U' hU' hU'aff).hom.f 0
        ((1 : B') ⊗ₜ[B, ψ'] sectionsToModel f' U' hU' F' s) =
      sectionsToModel f'' (fun j => g'' ⁻¹ᵁ U' j) (top_eq_iSup_preimage g'' U' hU')
        ((Scheme.Modules.pullback g'').obj F')
        (AlgebraicGeometry.pullbackSectionHom g'' F' ⊤ ⊤ (by simp) s) := by
  apply (baseAlternatingCechComplexXIso f'' (fun j => g'' ⁻¹ᵁ U' j)
    (top_eq_iSup_preimage g'' U' hU') ((Scheme.Modules.pullback g'').obj F')
      0).toLinearEquiv.injective
  have h := congr($(baseAlternatingCechComplexBaseChangeIso_hom_f_comp_XIso ψ' hsq' F' U' hU'
    hU'aff 0).hom ((1 : B') ⊗ₜ[B, ψ'] sectionsToModel f' U' hU' F' s))
  simp only [ModuleCat.hom_comp] at h
  refine h.trans ?_
  have h1 : (ModuleCat.extendScalars.{u, u, u} ψ').map
      (baseAlternatingCechComplexXIso f' U' hU' F' 0).hom
        ((1 : B') ⊗ₜ[B, ψ'] sectionsToModel f' U' hU' F' s) =
      (1 : B') ⊗ₜ[B, ψ'] Stacks.Cech.sectionsToAlternatingₗ f' U' F' (fun _ => le_top) s :=
    congrArg (fun z => (1 : B') ⊗ₜ[B, ψ'] z)
      (baseAlternatingCechComplexXIso_hom_sectionsToModel f' U' hU' F' s)
  refine (CategoryTheory.comp_apply _ _ _).trans ?_
  refine (congrArg _ h1).trans ?_
  refine (Stacks.Cech.alternatingCechModuleObjBaseChangeIso_hom_one_tmul g'' U'
    (fun j => g'' ⁻¹ᵁ U' j) (Equiv.refl I) F' (preimage_eq_preimage_equivRefl g'' U') ψ' f' f''
    (fun W => Stacks.Cech.baseRingHom_comp_app ψ' f' f'' g'' hsq' W) hsq' hU'aff 0 _).trans ?_
  refine (Stacks.Cech.alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ f' U' F'
    (fun _ => le_top) g'' (fun j => g'' ⁻¹ᵁ U' j) (Equiv.refl I)
    (preimage_eq_preimage_equivRefl g'' U') ψ' f''
    (fun W => Stacks.Cech.baseRingHom_comp_app ψ' f' f'' g'' hsq' W) s).trans ?_
  refine Eq.trans ?_ (baseAlternatingCechComplexXIso_hom_sectionsToModel f''
    (fun j => g'' ⁻¹ᵁ U' j) (top_eq_iSup_preimage g'' U' hU')
    ((Scheme.Modules.pullback g'').obj F') _).symm
  exact congrArg (Stacks.Cech.sectionsToAlternatingₗ f'' (fun j => g'' ⁻¹ᵁ U' j)
    ((Scheme.Modules.pullback g'').obj F') (fun _ => le_top))
    (pullbackSectionsBaseₗ_top_apply ψ' f' f'' g'' F'
      (fun W => Stacks.Cech.baseRingHom_comp_app ψ' f' f'' g'' hsq' W) s)

end SectionsBaseChange

section Comparison

/-- The termwise composition isomorphisms of extension of scalars satisfy the associativity
constraint, on complexes. -/
theorem extendScalarsComplexCompIso_hom_app_assoc {A₁ A₂ A₃ A₄ : Type u} [CommRing A₁]
    [CommRing A₂] [CommRing A₃] [CommRing A₄] (f₁ : A₁ →+* A₂) (f₂ : A₂ →+* A₃) (f₃ : A₃ →+* A₄)
    (K : CochainComplex (ModuleCat.{u} A₁) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} f₃).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((extendScalarsComplexCompIso f₁ f₂).hom.app K) ≫
      (extendScalarsComplexCompIso (f₂.comp f₁) f₃).hom.app K =
    (extendScalarsComplexCompIso f₂ f₃).hom.app (extendScalarsComplex f₁ K) ≫
      (extendScalarsComplexCompIso f₁ (f₃.comp f₂)).hom.app K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [extendScalarsComplexCompIso, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Iso.symm_hom]
  exact (extendScalarsComp_inv_app_assoc f₁ f₂ f₃ (K.X n)).symm

/-- A diagrammatic step for the cocycle identity. -/
theorem comp_eq_of_cocycle {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {P₀ Q₀ Q₁ Q₂ : C} {Z₀ Z₁ Z₂ Z₃ W₀ : D}
    (a : P₀ ⟶ Q₀) (b : Q₀ ⟶ Q₁) (c : Q₁ ⟶ Q₂) (k : G.obj Q₂ ⟶ Z₀) (m : Z₀ ⟶ Z₁)
    (s : G.obj Q₁ ⟶ Z₂) (d : Z₂ ⟶ Z₁) (x : G.obj Q₀ ⟶ Z₃) (r : Z₃ ⟶ Z₂)
    (p : G.obj P₀ ⟶ W₀) (q : W₀ ⟶ Z₃)
    (hcoc : G.map c ≫ k ≫ m = s ≫ d) (hnat : G.map a ≫ x = p ≫ q)
    (hpent : G.map b ≫ s = x ≫ r) :
    G.map (a ≫ b ≫ c) ≫ k ≫ m = p ≫ q ≫ r ≫ d := by
  rw [G.map_comp, G.map_comp, Category.assoc, Category.assoc, hcoc, ← Category.assoc (G.map b),
    hpent]
  simp only [← Category.assoc]
  rw [hnat]

variable {A R : Type u} [CommRing A] [CommRing R] (α : A →+* R)
  {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
  {I : Type u} [Finite I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))
  {P : CochainComplex (ModuleCat.{u} R) ℤ}
  (u : P ⟶ extendScalarsComplex α (baseAlternatingCechComplex f U hU F))

/-- **The chain-level comparison `P ⊗_R B ⟶ Č(X', F')`** for a model `u : P ⟶ Č ⊗_A R` over an
`A`-algebra `R` and an `R`-algebra `B`: extend the scalars of `u` along `ψ`, compose the two
extensions of scalars, and apply the Čech base-change isomorphism. -/
def kernelChainComparison {B : Type u} [CommRing B] (ψ : R →+* B) {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α)))) :
    extendScalarsComplex ψ P ⟶ baseAlternatingCechComplex f' (fun j => g' ⁻¹ᵁ U j)
      (top_eq_iSup_preimage g' U hU) ((Scheme.Modules.pullback g').obj F) :=
  ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫
    (extendScalarsComplexCompIso α ψ).hom.app (baseAlternatingCechComplex f U hU F) ≫
    (baseAlternatingCechComplexBaseChangeIso (ψ.comp α) hsq F U hU hUaff).hom

/-- Extending the scalars of the model `u` along any `R →+* B` stays a quasi-isomorphism. -/
private theorem quasiIso_extendScalars_map_model (hUaff : ∀ i, IsAffineOpen (U i))
    [QuasiIso u] [∀ n : ℤ, Module.Flat R (P.X n)] (hflat : IsFlatOver f.toLRSHom.toShHom F) (b : ℤ)
    [P.IsStrictlyLE b] {B : Type u} [CommRing B] (ψ : R →+* B) :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) := by
  have := Fintype.ofFinite I
  have : ∀ n : ℤ, Module.Flat R
      ((extendScalarsComplex α (baseAlternatingCechComplex f U hU F)).X n) := fun n => by
    have : Module.Flat A ((baseAlternatingCechComplex f U hU F).X n) :=
      flat_baseAlternatingCechComplex_X f U hU F hUaff hflat n
    let : Algebra A R := α.toAlgebra
    exact Module.Flat.baseChange A R ((baseAlternatingCechComplex f U hU F).X n)
  exact StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat ψ b (Fintype.card I : ℤ) u

/-- The chain-level comparison is a quasi-isomorphism. -/
theorem quasiIso_kernelChainComparison [QuasiIso u]
    [∀ n : ℤ, Module.Flat R (P.X n)] (hflat : IsFlatOver f.toLRSHom.toShHom F) (b : ℤ)
    [P.IsStrictlyLE b] {B : Type u} [CommRing B] (ψ : R →+* B) {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α)))) :
    QuasiIso (kernelChainComparison α F U hU hUaff u ψ hsq) := by
  have h1 := quasiIso_extendScalars_map_model α F U hU u hUaff hflat b ψ
  have h2 : IsIso (DerivedCategory.Q.map
      (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map u)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h1
  refine (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 ?_
  rw [kernelChainComparison, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **The cocycle square for the chain-level comparison.** -/
theorem kernelChainComparison_comp {B B' : Type u} [CommRing B] [CommRing B'] (ψ : R →+* B)
    (ψ' : B →+* B') {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)}
    {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α))))
    (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ'))) :
    haveI : IsSeparated f' := isSeparated_of_isPullback (ψ.comp α) hsq
    ((ModuleCat.extendScalars.{u, u, u} ψ').mapHomologicalComplex (ComplexShape.up ℤ)).map
          (kernelChainComparison α F U hU hUaff u ψ hsq) ≫
        (baseAlternatingCechComplexBaseChangeIso ψ' hsq' ((Scheme.Modules.pullback g').obj F)
            (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
            (isAffineOpen_preimage (ψ.comp α) hsq U hUaff)).hom ≫
        (baseAlternatingCechComplexMapIso f'' (fun j => (g'' ≫ g') ⁻¹ᵁ U j)
          (top_eq_iSup_preimage (g'' ≫ g') U hU)
          ((Scheme.Modules.pullbackComp g'' g').app F)).hom =
      (extendScalarsComplexCompIso ψ ψ').hom.app P ≫
        kernelChainComparison α F U hU hUaff u (ψ'.comp ψ)
          (Stacks.Cech.isPullback_comp_specMap (ψ.comp α) ψ' f f' f'' g' g'' hsq hsq') := by
  have : IsSeparated f' := isSeparated_of_isPullback (ψ.comp α) hsq
  exact comp_eq_of_cocycle _ _ _ _ _ _ _ _ _ _ _ _
    (baseAlternatingCechComplexBaseChangeIso_comp (ψ.comp α) ψ' hsq hsq' F U hU hUaff)
    ((extendScalarsComplexCompIso ψ ψ').hom.naturality u)
    (extendScalarsComplexCompIso_hom_app_assoc α ψ ψ' (baseAlternatingCechComplex f U hU F))

end Comparison

section Kernel

open scoped Matrix

variable {A R : Type u} [CommRing A] [CommRing R] (α : A →+* R)
  {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
  {I : Type u} [Fintype I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F)
  {P : CochainComplex (ModuleCat.{u} R) ℤ}
  (u : P ⟶ extendScalarsComplex α (baseAlternatingCechComplex f U hU F)) [QuasiIso u]
  [∀ n : ℤ, Module.Flat R (P.X n)] (b : ℤ) [P.IsStrictlyLE b] (hP : IsZero (P.X (-1)))
  {r β : ℕ} (e₀ : P.X 0 ≅ ModuleCat.of R (Fin r → R)) (e₁ : P.X 1 ≅ ModuleCat.of R (Fin β → R))
  (M : Matrix (Fin β) (Fin r) R) (hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv)

omit [∀ n : ℤ, Module.Flat R (P.X n)] in
include hM in
/-- The coordinates of `termEquiv` identify the kernel of `M.map ψ` with the degree-`0` cocycles
of `P ⊗_R B`. -/
theorem map_termEquiv_symm_ker {B : Type u} [CommRing B] (ψ : R →+* B) :
    (LinearMap.ker (M.map ψ).mulVecLin).map (termEquiv ψ e₀).symm.toLinearMap =
      LinearMap.ker ((extendScalarsComplex ψ P).d 0 1).hom := by
  ext x
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.mem_ker,
    Matrix.mulVecLin_apply, ← termEquiv_map ψ e₀ e₁ (P.d 0 1) M hM]
  exact (termEquiv ψ e₁).map_eq_zero_iff

/-- The degree-`0` cocycles of `P ⊗_R B` are the kernel of the matrix `M ⊗ B`. -/
def kerMatrixEquiv {B : Type u} [CommRing B] (ψ : R →+* B) :
    LinearMap.ker (M.map ψ).mulVecLin ≃ₗ[B] LinearMap.ker ((extendScalarsComplex ψ P).d 0 1).hom :=
  (termEquiv ψ e₀).symm.ofSubmodules _ _ (map_termEquiv_symm_ker e₀ e₁ M hM ψ)

omit [∀ n : ℤ, Module.Flat R (P.X n)] in
/-- `kerMatrixEquiv` is the inverse of the coordinate identification. -/
theorem kerMatrixEquiv_apply_coe {B : Type u} [CommRing B] (ψ : R →+* B)
    (v : LinearMap.ker (M.map ψ).mulVecLin) :
    (kerMatrixEquiv e₀ e₁ M hM ψ v : (extendScalarsComplex ψ P).X 0) =
      (termEquiv ψ e₀).symm v := rfl

omit [∀ n : ℤ, Module.Flat R (P.X n)] in
include hP in
/-- The differential of `P ⊗_R B` into degree `0` vanishes when `P` vanishes in degree `-1`. -/
theorem d_neg_one_zero_extendScalarsComplex {B : Type u} [CommRing B] (ψ : R →+* B) :
    (extendScalarsComplex ψ P).d (-1) 0 = 0 :=
  ((ModuleCat.extendScalars.{u, u, u} ψ).map_isZero hP).eq_of_src _ _

omit [Fintype I] in
/-- The differential of the `ℤ`-indexed Čech model into degree `0` vanishes. -/
theorem d_neg_one_zero_baseAlternatingCechComplex {B : Type u} [CommRing B] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of B)) (U' : I → X'.Opens) (hU' : (⊤ : X'.Opens) = ⨆ i, U' i)
    (F' : X'.Modules) : (baseAlternatingCechComplex f' U' hU' F').d (-1) 0 = 0 :=
  (isZero_baseAlternatingCechComplex_X_of_neg f' U' hU' F' (-1) (by omega)).eq_of_src _ _

/-- **The kernel model over an `R`-algebra.** For an `R`-algebra `B` and a cartesian square
exhibiting `X'` as the base change of `X` to `B`, the kernel of `M ⊗ B` is the module of global
sections of the pullback of `F` to `X'`. -/
def kernelModelEquiv {B : Type u} [CommRing B] (ψ : R →+* B) {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α)))) :
    letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj F) ⊤
    LinearMap.ker (M.map ψ).mulVecLin ≃ₗ[B] Γ((Scheme.Modules.pullback g').obj F, ⊤) :=
  letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj F) ⊤
  haveI := quasiIso_kernelChainComparison α F U hU hUaff u hflat b ψ hsq
  (kerMatrixEquiv e₀ e₁ M hM ψ).trans
    ((LinearEquiv.ofBijective (kerRestrict (kernelChainComparison α F U hU hUaff u ψ hsq))
      (bijective_kerRestrict _ (d_neg_one_zero_extendScalarsComplex hP ψ)
        (d_neg_one_zero_baseAlternatingCechComplex _ _ _ _))).trans
      (sectionsEquivKer f' (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
        ((Scheme.Modules.pullback g').obj F)).symm)

/-- The kernel model is characterized by the chain-level comparison in degree `0`. -/
theorem sectionsToModel_kernelModelEquiv {B : Type u} [CommRing B] (ψ : R →+* B)
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α))))
    (v : LinearMap.ker (M.map ψ).mulVecLin) :
    sectionsToModel f' (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
        ((Scheme.Modules.pullback g').obj F)
        (kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq v) =
      (kernelChainComparison α F U hU hUaff u ψ hsq).f 0 ((termEquiv ψ e₀).symm v) := by
  rw [← sectionsEquivKer_apply_coe]
  simp only [kernelModelEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

open scoped ChangeOfRings TensorProduct in
/-- **The kernel model is natural in the algebra.** -/
theorem kernelModelEquiv_comp {B B' : Type u} [CommRing B] [CommRing B'] (ψ : R →+* B)
    (ψ' : B →+* B') {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)}
    {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ.comp α))))
    (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ')))
    (hsq'' : IsPullback (g'' ≫ g') f'' f (Spec.map (CommRingCat.ofHom ((ψ'.comp ψ).comp α))))
    (v : LinearMap.ker (M.map ψ).mulVecLin)
    (hv : ψ' ∘ (v : Fin r → B) ∈ LinearMap.ker (M.map (ψ'.comp ψ)).mulVecLin) :
    ((Scheme.Modules.pullbackComp g'' g').hom.app F).app ⊤
        (AlgebraicGeometry.pullbackSectionHom g'' ((Scheme.Modules.pullback g').obj F) ⊤ ⊤
          (by simp) (kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq v)) =
      kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM (ψ'.comp ψ) hsq''
        ⟨ψ' ∘ (v : Fin r → B), hv⟩ := by
  have : IsSeparated f' := isSeparated_of_isPullback (ψ.comp α) hsq
  set s := kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq v with hs
  apply sectionsToModel_injective f'' (fun j => (g'' ≫ g') ⁻¹ᵁ U j)
    (top_eq_iSup_preimage (g'' ≫ g') U hU)
  refine Eq.trans ?_ (sectionsToModel_kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM
    (ψ'.comp ψ) hsq'' ⟨ψ' ∘ (v : Fin r → B), hv⟩).symm
  set z := (termEquiv ψ e₀).symm v with hz
  have hy : (termEquiv (ψ'.comp ψ) e₀).symm (ψ' ∘ (v : Fin r → B)) =
      (ModuleCat.extendScalarsComp ψ ψ').inv.app (P.X 0) ((1 : B') ⊗ₜ[B, ψ'] z) := by
    apply (termEquiv (ψ'.comp ψ) e₀).injective
    rw [LinearEquiv.apply_symm_apply, termEquiv_comp, hz, LinearEquiv.apply_symm_apply]
  have hcoc := congr($((kernelChainComparison_comp α F U hU hUaff u ψ ψ' hsq hsq')).f 0)
  have hcoc' := congr($(hcoc).hom ((1 : B') ⊗ₜ[B, ψ'] z))
  change _ = (kernelChainComparison α F U hU hUaff u (ψ'.comp ψ) hsq'').f 0
      ((termEquiv (ψ'.comp ψ) e₀).symm (ψ' ∘ (v : Fin r → B)))
  rw [hy]
  have h1 : (((ModuleCat.extendScalars.{u, u, u} ψ').mapHomologicalComplex
      (ComplexShape.up ℤ)).map (kernelChainComparison α F U hU hUaff u ψ hsq)).f 0
        ((1 : B') ⊗ₜ[B, ψ'] z) = (1 : B') ⊗ₜ[B, ψ'] (sectionsToModel f' (fun j => g' ⁻¹ᵁ U j)
          (top_eq_iSup_preimage g' U hU) ((Scheme.Modules.pullback g').obj F) s) :=
    congrArg (fun y => (1 : B') ⊗ₜ[B, ψ'] y)
      (sectionsToModel_kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM ψ hsq v).symm
  have e2 := congrArg (fun y => (baseAlternatingCechComplexMapIso f'' (fun j => (g'' ≫ g') ⁻¹ᵁ U j)
      (top_eq_iSup_preimage (g'' ≫ g') U hU) ((Scheme.Modules.pullbackComp g'' g').app F)).hom.f 0
      ((baseAlternatingCechComplexBaseChangeIso ψ' hsq' ((Scheme.Modules.pullback g').obj F)
        (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
        (isAffineOpen_preimage (ψ.comp α) hsq U hUaff)).hom.f 0 y)) h1
  have g1 := baseChangeIso_sectionsToModel ψ' hsq' ((Scheme.Modules.pullback g').obj F)
    (fun j => g' ⁻¹ᵁ U j) (top_eq_iSup_preimage g' U hU)
    (isAffineOpen_preimage (ψ.comp α) hsq U hUaff) s
  have g2 := sectionsToModel_mapIso f'' (fun j => (g'' ≫ g') ⁻¹ᵁ U j)
    (top_eq_iSup_preimage (g'' ≫ g') U hU) ((Scheme.Modules.pullbackComp g'' g').app F)
    (AlgebraicGeometry.pullbackSectionHom g'' ((Scheme.Modules.pullback g').obj F) ⊤ ⊤
      (by simp) s)
  exact g2.symm.trans ((congrArg (fun y => (baseAlternatingCechComplexMapIso f''
      (fun j => (g'' ≫ g') ⁻¹ᵁ U j) (top_eq_iSup_preimage (g'' ≫ g') U hU)
      ((Scheme.Modules.pullbackComp g'' g').app F)).hom.f 0 y) g1.symm).trans
    (e2.symm.trans hcoc'))

/-- The kernel model depends only on the ring map, not on how the cartesian square is presented. -/
theorem kernelModelEquiv_congr {B : Type u} [CommRing B] {ψ₁ ψ₂ : R →+* B} (h : ψ₁ = ψ₂)
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq₁ : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ₁.comp α))))
    (hsq₂ : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (ψ₂.comp α))))
    (y₁ : LinearMap.ker (M.map ψ₁).mulVecLin) (y₂ : LinearMap.ker (M.map ψ₂).mulVecLin)
    (hy : (y₁ : Fin r → B) = y₂) :
    kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM ψ₁ hsq₁ y₁ =
      kernelModelEquiv α F U hU hUaff hflat u b hP e₀ e₁ M hM ψ₂ hsq₂ y₂ := by
  subst h
  obtain rfl : y₁ = y₂ := Subtype.ext hy
  rfl

end Kernel

section Minimality

open scoped Matrix

variable {R : Type u} [CommRing R] {P : CochainComplex (ModuleCat.{u} R) ℤ}
  (hP : IsZero (P.X (-1)))
  {r β : ℕ} (e₀ : P.X 0 ≅ ModuleCat.of R (Fin r → R)) (e₁ : P.X 1 ≅ ModuleCat.of R (Fin β → R))
  (M : Matrix (Fin β) (Fin r) R) (hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv)

include hP hM in
/-- **Minimality.** If after extension of scalars to a field the degree-`0` homology of `P` has
the dimension of the degree-`0` term, the matrix of the first differential vanishes over the
field. -/
theorem matrix_map_eq_zero_of_finrank {k : Type u} [Field k] (χ : R →+* k)
    (hr : Module.finrank k ((extendScalarsComplex χ P).homology 0) = r) : M.map χ = 0 := by
  classical
  let V := extendScalarsComplex χ P
  have hV : V.d (-1) 0 = 0 := ((ModuleCat.extendScalars.{u, u, u} χ).map_isZero hP).eq_of_src _ _
  have hker : Module.finrank k (LinearMap.ker (V.d 0 1).hom) = r :=
    ((homologyZeroIsoKer V hV).toLinearEquiv.finrank_eq).symm.trans hr
  have hX : Module.finrank k (V.X 0) = r :=
    (termEquiv χ e₀).finrank_eq.trans (Module.finrank_fin_fun k)
  have : Module.Finite k (V.X 0) := Module.Finite.equiv (termEquiv χ e₀).symm
  have htop : LinearMap.ker (V.d 0 1).hom = ⊤ :=
    Submodule.eq_top_of_finrank_eq (hker.trans hX.symm)
  have hzero : ∀ w : Fin r → k, M.map χ *ᵥ w = 0 := fun w => by
    have h1 := termEquiv_map χ e₀ e₁ (P.d 0 1) M hM ((termEquiv χ e₀).symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [← h1]
    have h2 : ((termEquiv χ e₀).symm w) ∈ LinearMap.ker (V.d 0 1).hom := by simp [htop]
    rw [LinearMap.mem_ker] at h2
    change termEquiv χ e₁ ((V.d 0 1).hom ((termEquiv χ e₀).symm w)) = 0
    rw [h2, map_zero]
  ext i j
  have := congrFun (hzero (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa using this

end Minimality

section Main

open scoped Matrix

/-- Equal ring maps to a field give homology of the same dimension. -/
theorem finrank_homology_extendScalarsComplex_congr {A k : Type u} [CommRing A] [Field k]
    {φ₁ φ₂ : A →+* k} (h : φ₁ = φ₂) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Module.finrank k ((extendScalarsComplex φ₁ K).homology i) =
      Module.finrank k ((extendScalarsComplex φ₂ K).homology i) := by
  subst h
  rfl

/-- A vector in the kernel of a matrix stays in the kernel after a ring map. -/
theorem comp_mem_ker_mulVecLin_map {R₀ B B' : Type u} [CommRing R₀] [CommRing B] [CommRing B']
    {m n : ℕ} (N : Matrix (Fin m) (Fin n) R₀) (ψ₀ : R₀ →+* B) (ψ : B →+* B') (v : Fin n → B)
    (hv : v ∈ LinearMap.ker (N.map ψ₀).mulVecLin) :
    ψ ∘ v ∈ LinearMap.ker (N.map (ψ.comp ψ₀)).mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  funext i
  have h := RingHom.map_mulVec ψ (N.map ψ₀) v i
  rw [hv, Pi.zero_apply, map_zero, Matrix.map_map] at h
  exact h.symm

/-- Rescaling a matrix by a unit does not change its kernel. -/
theorem ker_mulVecLin_smul {B : Type u} [CommRing B] {m n : ℕ} (N : Matrix (Fin m) (Fin n) B)
    {c : B} (hc : IsUnit c) :
    LinearMap.ker (c • N).mulVecLin = LinearMap.ker N.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  exact hc.smul_eq_zero

/-- **Clearing denominators.** A power of `g` times a matrix over `A_g` is the image of a matrix
`D` over `A`, and then `D ⊗ B = g^N • (M ⊗ B)` for every ring map out of `A` inverting `g`. -/
theorem exists_matrix_map_eq_pow_smul {A : Type u} [CommRing A] (g : A) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (Localization.Away g)) :
    ∃ (N : ℕ) (D : Matrix (Fin m) (Fin n) A),
      (∀ i j, algebraMap A (Localization.Away g) (D i j) =
        algebraMap A (Localization.Away g) (g ^ N) * M i j) ∧
      ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g)),
        D.map φ = φ g ^ N • M.map (IsLocalization.Away.lift g hgφ) := by
  classical
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g)
    (Finset.univ : Finset (Fin m × Fin n)) (fun ij => M ij.1 ij.2)
  have hN' : ∀ i j, ∃ a : A, algebraMap A (Localization.Away g) a =
      algebraMap A (Localization.Away g) (g ^ N) * M i j := fun i j => by
    obtain ⟨a, ha⟩ := hN (i, j) (Finset.mem_univ _)
    exact ⟨a, ha.trans (Algebra.smul_def _ _)⟩
  choose D hD using hN'
  refine ⟨N, Matrix.of D, hD, fun {B} _ φ hgφ => ?_⟩
  ext i j
  have h := congrArg (IsLocalization.Away.lift g hgφ) (hD i j)
  rw [← RingHom.comp_apply, IsLocalization.Away.lift_comp, map_mul, ← RingHom.comp_apply,
    IsLocalization.Away.lift_comp, map_pow] at h
  simpa [Matrix.map_apply] using h

/-- The homology of the derived extension of scalars of the Čech model is that of its termwise
extension of scalars. -/
def homologyTotalDerivedExtensionScalarsIso {A B : Type u} [CommRing A] [CommRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsSeparated f] {I : Type u} [Fintype I]
    [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)
    [F.IsQuasicoherent] (φ : A →+* B) (hUaff : ∀ i, IsAffineOpen (U i))
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj (DerivedCategory.Q.obj (baseAlternatingCechComplex f U hU F))) ≅
      (extendScalarsComplex φ (baseAlternatingCechComplex f U hU F)).homology i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso
      (totalDerivedExtensionScalarsModelIso f U hU F φ hUaff hflat) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).app _

/-- A bounded complex of free modules maps by a quasi-isomorphism to every complex isomorphic to
it in the derived category. -/
theorem exists_quasiIso_of_iso_Q {R : Type u} [CommRing R]
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    {d : ℤ → ℕ} (hPX : ∀ n, Nonempty (P.X n ≅ ModuleCat.of R (ULift.{u} (Fin (d n) → R))))
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K) : ∃ u : P ⟶ K, QuasiIso u := by
  have : ∀ n, Projective (P.X n) := fun n =>
    Projective.of_iso (hPX n).some.symm
      (ModuleCat.projective_of_free (Module.Free.chooseBasis R _))
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨u, hu⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective P K e.hom
  refine ⟨u, (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 ?_⟩
  rw [hu]
  infer_instance

section KernelMinimality

variable {A R : Type u} [CommRing A] [CommRing R] (α : A →+* R)
  {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
  {I : Type u} [Finite I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F)
  {P : CochainComplex (ModuleCat.{u} R) ℤ}
  (u : P ⟶ extendScalarsComplex α (baseAlternatingCechComplex f U hU F)) [QuasiIso u]
  [∀ n : ℤ, Module.Flat R (P.X n)] (b : ℤ) [P.IsStrictlyLE b] (hP : IsZero (P.X (-1)))
  {r β : ℕ} (e₀ : P.X 0 ≅ ModuleCat.of R (Fin r → R)) (e₁ : P.X 1 ≅ ModuleCat.of R (Fin β → R))
  (M : Matrix (Fin β) (Fin r) R) (hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv)

include hUaff hflat u b hP e₀ e₁ hM in
/-- **Minimality for the Čech model.** If over a field the degree-`0` homology of the Čech model
has the rank of `P⁰`, the matrix of `P⁰ ⟶ P¹` vanishes over the field. -/
theorem matrix_map_eq_zero_of_finrank_cech {k : Type u} [Field k] (χ : R →+* k)
    (hr : Module.finrank k ((extendScalarsComplex (χ.comp α)
      (baseAlternatingCechComplex f U hU F)).homology 0) = r) : M.map χ = 0 := by
  have := Fintype.ofFinite I
  have := quasiIso_extendScalars_map_model α F U hU u hUaff hflat b χ
  exact matrix_map_eq_zero_of_finrank hP e₀ e₁ M hM χ
    ((isoOfQuasiIsoAt (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) 0).toLinearEquiv.finrank_eq.trans
      ((((HomologicalComplex.homologyFunctor _ _ 0).mapIso
        ((extendScalarsComplexCompIso α χ).app
          (baseAlternatingCechComplex f U hU F))).toLinearEquiv.finrank_eq).trans hr))

end KernelMinimality

section Away

variable {A : Type u} [CommRing A] (g : A)
  {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
  {I : Type u} [Fintype I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i)) (hflat : IsFlatOver f.toLRSHom.toShHom F)
  {P : CochainComplex (ModuleCat.{u} (Localization.Away g)) ℤ}
  (u : P ⟶ extendScalarsComplex (algebraMap A (Localization.Away g))
    (baseAlternatingCechComplex f U hU F)) [QuasiIso u]
  [∀ n : ℤ, Module.Flat (Localization.Away g) (P.X n)] (b : ℤ) [P.IsStrictlyLE b]
  (hP : IsZero (P.X (-1))) {r β : ℕ}
  (e₀ : P.X 0 ≅ ModuleCat.of (Localization.Away g) (Fin r → Localization.Away g))
  (e₁ : P.X 1 ≅ ModuleCat.of (Localization.Away g) (Fin β → Localization.Away g))
  (M : Matrix (Fin β) (Fin r) (Localization.Away g))
  (hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv)

omit [Fintype I] in
include hUaff hflat u b hP e₀ e₁ hM in
/-- **A matrix over `A` with entries in `p` cutting out the kernels of `M`.** If over `κ(p)` the
degree-`0` homology of the Čech model has the rank of `P⁰`, there is a matrix `D` over `A` with
entries in `p` such that `ker (D ⊗ B) = ker (M ⊗ B)` for every ring map out of `A` inverting `g`.
-/
theorem exists_matrix_mem_ker_eq [Finite I] (p : Ideal A) [p.IsPrime] (hg : g ∉ p)
    (hr : Module.finrank p.ResidueField ((extendScalarsComplex (algebraMap A p.ResidueField)
      (baseAlternatingCechComplex f U hU F)).homology 0) = r) :
    ∃ D : Matrix (Fin β) (Fin r) A, (∀ i j, D i j ∈ p) ∧
      ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g)),
        LinearMap.ker (D.map φ).mulVecLin =
          LinearMap.ker (M.map (IsLocalization.Away.lift g hgφ)).mulVecLin := by
  have hgκ : IsUnit (algebraMap A p.ResidueField g) := by
    refine isUnit_iff_ne_zero.2 fun h => hg ?_
    rw [← Ideal.ker_algebraMap_residueField p]
    exact h
  have hχ := IsLocalization.Away.lift_comp (S := Localization.Away g) g hgκ
  have hMχ := matrix_map_eq_zero_of_finrank_cech _ F U hU hUaff hflat u b hP e₀ e₁ M hM
    (IsLocalization.Away.lift g hgκ)
    ((finrank_homology_extendScalarsComplex_congr hχ (baseAlternatingCechComplex f U hU F)
      0).trans hr)
  obtain ⟨N, D, hD, hDφ⟩ := exists_matrix_map_eq_pow_smul g M
  refine ⟨D, fun i j => ?_, fun φ hgφ => by rw [hDφ φ hgφ, ker_mulVecLin_smul _ (hgφ.pow N)]⟩
  rw [← Ideal.ker_algebraMap_residueField p, RingHom.mem_ker, ← hχ, RingHom.comp_apply, hD,
    map_mul]
  have := congrFun (congrFun hMχ i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [this, mul_zero]

variable (D : Matrix (Fin β) (Fin r) A)
  (hker : ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g)),
    LinearMap.ker (D.map φ).mulVecLin =
      LinearMap.ker (M.map (IsLocalization.Away.lift g hgφ)).mulVecLin)

/-- **The kernel model over `A_g`, read on a matrix `D` over `A`.** For every ring map
`φ : A ⟶ B` inverting `g`, the kernel of `D ⊗ B` is the module of global sections of the pullback
of `F` to the base change of `X` to `B`. -/
def awayKernelModelEquiv {B : Type u} [CommRing B] (φ : A →+* B) (hgφ : IsUnit (φ g))
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))) :
    letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj F) ⊤
    LinearMap.ker (D.map φ).mulVecLin ≃ₗ[B] Γ((Scheme.Modules.pullback g').obj F, ⊤) :=
  (LinearEquiv.ofEq _ _ (hker φ hgφ)).trans
    (kernelModelEquiv (algebraMap A (Localization.Away g)) F U hU hUaff hflat u b hP e₀ e₁ M hM
      (IsLocalization.Away.lift g hgφ) (by rwa [IsLocalization.Away.lift_comp]))

/-- **`awayKernelModelEquiv` is natural in the algebra.** -/
theorem awayKernelModelEquiv_comp {B B' : Type u} [CommRing B] [CommRing B'] (φ : A →+* B)
    (ψ : B →+* B') (hgφ : IsUnit (φ g)) {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)}
    {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
    (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
    (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ)))
    (v : LinearMap.ker (D.map φ).mulVecLin) :
    ((Scheme.Modules.pullbackComp g'' g').hom.app F).app ⊤
        (AlgebraicGeometry.pullbackSectionHom g'' ((Scheme.Modules.pullback g').obj F) ⊤ ⊤
          (by simp)
          (awayKernelModelEquiv g F U hU hUaff hflat u b hP e₀ e₁ M hM D hker φ hgφ hsq v)) =
      awayKernelModelEquiv g F U hU hUaff hflat u b hP e₀ e₁ M hM D hker (ψ.comp φ) (hgφ.map ψ)
        (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g' g'' hsq hsq')
        ⟨ψ ∘ (v : Fin r → B), comp_mem_ker_mulVecLin_map D φ ψ _ v.2⟩ := by
  have hsq₁ : IsPullback g' f' f (Spec.map (CommRingCat.ofHom
      ((IsLocalization.Away.lift g hgφ).comp (algebraMap A (Localization.Away g))))) := by
    rwa [IsLocalization.Away.lift_comp]
  have hcomp : ψ.comp (IsLocalization.Away.lift (S := Localization.Away g) g hgφ) =
      IsLocalization.Away.lift (S := Localization.Away g) (g := ψ.comp φ) g (hgφ.map ψ) :=
    IsLocalization.ringHom_ext (Submonoid.powers g) (by
      rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp])
  let v' := LinearEquiv.ofEq _ _ (hker φ hgφ) v
  have hsq'' : IsPullback (g'' ≫ g') f'' f (Spec.map (CommRingCat.ofHom
      ((ψ.comp (IsLocalization.Away.lift g hgφ)).comp (algebraMap A (Localization.Away g))))) :=
    Stacks.Cech.isPullback_comp_specMap _ ψ f f' f'' g' g'' hsq₁ hsq'
  have key := kernelModelEquiv_comp (algebraMap A (Localization.Away g)) F U hU hUaff hflat u b hP
    e₀ e₁ M hM (IsLocalization.Away.lift g hgφ) ψ hsq₁ hsq' hsq'' v'
    (comp_mem_ker_mulVecLin_map M _ ψ _ v'.2)
  rw [awayKernelModelEquiv, awayKernelModelEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply]
  convert key using 1
  have hc := kernelModelEquiv_congr (algebraMap A (Localization.Away g)) F U hU hUaff hflat u b hP
    e₀ e₁ M hM hcomp.symm
    (by
      rw [IsLocalization.Away.lift_comp]
      exact Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g' g'' hsq hsq')
    hsq''
    (LinearEquiv.ofEq _ _ (hker (ψ.comp φ) (hgφ.map ψ)) ⟨ψ ∘ (v : Fin r → B),
      comp_mem_ker_mulVecLin_map D φ ψ _ v.2⟩)
    ⟨ψ ∘ (v' : Fin r → B), comp_mem_ker_mulVecLin_map M _ ψ _ v'.2⟩ rfl
  convert hc using 2

end Away

/-- **Cohomology and base change in degree `0`: a minimal local kernel model** (cf. the proof of
[Stacks, Tag 0BDL]). Let `A` be Noetherian, `f : X ⟶ Spec A` proper and `F` a coherent
`𝒪_X`-module flat over `A`, and let `p` be a prime of `A`. There are `g ∉ p` and a `β × r`
matrix `D` over `A` with all entries in `p` such that for every `A`-algebra `φ : A ⟶ B` in which
`g` is invertible and every cartesian square exhibiting `X'` as `X ×_A B`, the `B`-module
`Γ(X', F_{X'})` is identified with `ker(D ⊗ B : B^r → B^β)`, and these identifications are
natural in `B`: pulling the section attached to `v` back along a further base change
`X'' = X' ×_B B'` and transporting it by the composition isomorphism of pullbacks gives the
section attached to the image of `v` in `B'^r`. -/
theorem exists_away_kernelModel {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (F : X.Modules) [F.IsCoherent]
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
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨I, hIfin, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  let := hIlin
  have := hIfin
  let C := baseAlternatingCechComplex f U hU F
  have hpc := StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} (DerivedCategory.Q.obj C)
    (isPerfect_Q_baseAlternatingCechComplex f U hU F hUaff haff hflat)
  let κ := p.ResidueField
  have hvan : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C))) := fun i hi => by
    refine IsZero.of_iso ?_
      (homologyTotalDerivedExtensionScalarsIso f U hU F (algebraMap A κ) hUaff hflat i)
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A κ)).map_isZero
        (isZero_baseAlternatingCechComplex_X_of_neg f U hU F i hi))
  obtain ⟨g, hg, -, P, b, hPge, hPle, hPX, ⟨eP⟩⟩ :=
    StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below
      p (DerivedCategory.Q.obj C) hpc ⟨0, inferInstance⟩ 0 hvan
  let Ag := Localization.Away g
  let α := algebraMap A Ag
  let r := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 0).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C)))
  let β := Module.finrank κ ((DerivedCategory.homologyFunctor (ModuleCat.{u} κ) 1).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A κ)).functor.obj (DerivedCategory.Q.obj C)))
  have : P.IsStrictlyLE b := hPle
  have : P.IsStrictlyGE 0 := hPge
  have : ∀ n, Module.Flat Ag (P.X n) := fun n =>
    Module.Flat.of_linearEquiv (hPX n).some.toLinearEquiv
  obtain ⟨u, _⟩ := exists_quasiIso_of_iso_Q P (extendScalarsComplex α C) 0 b hPX
    (eP ≪≫ totalDerivedExtensionScalarsModelIso f U hU F α hUaff hflat)
  have hP : IsZero (P.X (-1)) := P.isZero_of_isStrictlyGE 0 (-1)
  let e₀ : P.X 0 ≅ ModuleCat.of Ag (Fin r → Ag) :=
    (hPX 0).some ≪≫ (ULift.moduleEquiv (R := Ag) (M := Fin r → Ag)).toModuleIso
  let e₁ : P.X 1 ≅ ModuleCat.of Ag (Fin β → Ag) :=
    (hPX 1).some ≪≫ (ULift.moduleEquiv (R := Ag) (M := Fin β → Ag)).toModuleIso
  let M := LinearMap.toMatrix' (e₁.hom.hom ∘ₗ (P.d 0 1).hom ∘ₗ e₀.inv.hom)
  have hM : P.d 0 1 = e₀.hom ≫ ModuleCat.ofHom M.mulVecLin ≫ e₁.inv := by
    ext x
    simp [M]
  obtain ⟨D, hDp, hker⟩ := exists_matrix_mem_ker_eq g F U hU hUaff hflat u b hP e₀ e₁ M hM p hg
    (homologyTotalDerivedExtensionScalarsIso f U hU F _ hUaff hflat 0).toLinearEquiv.finrank_eq.symm
  refine ⟨g, hg, r, β, D, hDp, fun {B} _ φ hgφ X' f' g' hsq =>
    awayKernelModelEquiv g F U hU hUaff hflat u b hP e₀ e₁ M hM D hker φ hgφ hsq, ?_⟩
  intro B B' _ _ φ ψ hgφ X' X'' f' f'' g' g'' hsq hsq' v
  have key := awayKernelModelEquiv_comp g F U hU hUaff hflat u b hP e₀ e₁ M hM D hker φ ψ hgφ hsq
    hsq' v
  convert key using 3

end Main

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
