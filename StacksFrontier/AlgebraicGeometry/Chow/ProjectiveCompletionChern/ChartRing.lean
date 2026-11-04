module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.Chart
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.AdjoinDegreeOneChart
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenSections
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# The ring of functions on `T ≠ 0` over an affine open

Let `E = Proj_X(Sym^*(𝒞)[T])` be the projective completion of the vector bundle of `𝒞` and `V`
an affine open of `X`, with `R = Γ(X, V)` and `M = Γ(𝒞, V)`. The sections of `𝒞 ⊕ 𝒪_X` over `V`
are `M × R`, the graded ring `Γ(V, Sym^*(𝒞 ⊕ 𝒪_X))` is `Sym_R(M × R)`, and the degree-zero part
of its localization at `T` is `Sym_R(M)`. This file records these identifications.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.sectionsSplit`: `Γ(𝒞 ⊕ 𝒪_X, V) ≃ Γ(𝒞, V) × Γ(X, V)`.
* `Stacks.Chow.ProjectiveCompletion.chartGradedHom`,
  `Stacks.Chow.ProjectiveCompletion.chartGradedInv`: the graded ring isomorphism
  `Γ(V, Sym^*(𝒞 ⊕ 𝒪_X)) ≅ Sym_R(M × R)`.
* `Stacks.Chow.ProjectiveCompletion.chartAwayEquiv`: the induced isomorphism of the degree-zero
  localizations at `T`, landing in `Sym_R(M)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj HomogeneousLocalization

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules) (V : X.Opens)

/-- The projection `𝒞 ⊕ 𝒪_X ⟶ 𝒞`. -/
def fst : module 𝒞 ⟶ 𝒞 := biprod.fst

/-- The projections and inclusions of `𝒞 ⊕ 𝒪_X` satisfy `fst ≫ inl + snd ≫ inr = 𝟙`. -/
theorem fst_inl_add_snd_inr : fst 𝒞 ≫ inl 𝒞 + snd 𝒞 ≫ inr 𝒞 = 𝟙 (module 𝒞) := biprod.total

/-- The inclusion of `𝒞` followed by the projection to `𝒞` is the identity. -/
theorem inl_fst : inl 𝒞 ≫ fst 𝒞 = 𝟙 𝒞 := biprod.inl_fst

/-- The inclusion of `𝒪_X` followed by the projection to `𝒞` is zero. -/
theorem inr_fst : inr 𝒞 ≫ fst 𝒞 = 0 := biprod.inr_fst

/-- The inclusion of `𝒪_X` followed by the projection to `𝒪_X` is the identity. -/
theorem inr_snd : inr 𝒞 ≫ snd 𝒞 = 𝟙 _ := biprod.inr_snd

/-- A morphism of modules is additive on sections. -/
theorem app_add {M N : X.Modules} (f : M ⟶ N) (a b : Γ(M, V)) :
    Scheme.Modules.Hom.app f V (a + b) =
      Scheme.Modules.Hom.app f V a + Scheme.Modules.Hom.app f V b :=
  (ConcreteCategory.hom (Scheme.Modules.Hom.app f V)).map_add a b

/-- A composite of morphisms of modules on sections. -/
theorem app_comp {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (a : Γ(M, V)) :
    Scheme.Modules.Hom.app (f ≫ g) V a =
      Scheme.Modules.Hom.app g V (Scheme.Modules.Hom.app f V a) := rfl

/-- The structure sheaf as a module, at the `X.Modules` spelling. -/
abbrev unitM : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- A function is a section of the structure sheaf. -/
def toUnitM (a : Γ(X, V)) : Γ(unitM (X := X), V) := a

/-- **The sections of `𝒞 ⊕ 𝒪_X` over an open `V`** are pairs of a section of `𝒞` and a
function. -/
def sectionsSplit : Γ(module 𝒞, V) ≃ₗ[Γ(X, V)] Γ(𝒞, V) × Γ(X, V) where
  toFun x := (Scheme.Modules.Hom.app (fst 𝒞) V x, Scheme.Modules.Hom.app (snd 𝒞) V x)
  invFun p :=
    Scheme.Modules.Hom.app (inl 𝒞) V p.1 + Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V p.2)
  map_add' x y := Prod.ext (app_add V _ x y) (app_add V _ x y)
  map_smul' r x := Prod.ext (Scheme.Modules.Hom.app_smul _ r x)
    (Scheme.Modules.Hom.app_smul _ r x)
  left_inv x := by
    have h := congrArg (fun f => Scheme.Modules.Hom.app f V x) (fst_inl_add_snd_inr 𝒞)
    simp only [Scheme.Modules.Hom.add_app, Scheme.Modules.Hom.id_app] at h
    exact h
  right_inv p := by
    refine Prod.ext ?_ ?_
    · have e1 : Scheme.Modules.Hom.app (fst 𝒞) V (Scheme.Modules.Hom.app (inl 𝒞) V p.1) = p.1 :=
        congrArg (fun f => Scheme.Modules.Hom.app f V p.1) (inl_fst 𝒞)
      have e2 :
          Scheme.Modules.Hom.app (fst 𝒞) V (Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V p.2)) = 0 :=
        congrArg (fun f => Scheme.Modules.Hom.app f V (toUnitM V p.2)) (inr_fst 𝒞)
      change Scheme.Modules.Hom.app (fst 𝒞) V
        (Scheme.Modules.Hom.app (inl 𝒞) V p.1 +
          Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V p.2)) = p.1
      rw [app_add, e1, e2, add_zero]
    · have e1 : Scheme.Modules.Hom.app (snd 𝒞) V (Scheme.Modules.Hom.app (inl 𝒞) V p.1) = 0 :=
        congrArg (fun f => Scheme.Modules.Hom.app f V p.1) (inl_snd 𝒞)
      have e2 : Scheme.Modules.Hom.app (snd 𝒞) V
          (Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V p.2)) = toUnitM V p.2 :=
        congrArg (fun f => Scheme.Modules.Hom.app f V (toUnitM V p.2)) (inr_snd 𝒞)
      change Scheme.Modules.Hom.app (snd 𝒞) V
        (Scheme.Modules.Hom.app (inl 𝒞) V p.1 +
          Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V p.2)) = toUnitM V p.2
      rw [app_add, e1, e2]
      exact zero_add _

/-! ### The graded ring of sections over an affine open -/

section Graded

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] {V}
  (hV : IsAffineOpen V)

/-- The module `𝒞 ⊕ 𝒪_X` is quasi-coherent. -/
instance isQuasicoherent_module : (module 𝒞).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _

/-- The ring isomorphism `Γ(V, Sym^*(𝒞 ⊕ 𝒪_X)) ≅ Sym_R(M × R)`, as a ring homomorphism. -/
def chartRingHom :
    (symAlg 𝒞).sectionRing V →+* SymmetricAlgebra Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) :=
  (SymPow.symAlgMap (sectionsSplit 𝒞 V).toLinearMap).toRingHom.comp
    (AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))).toRingHom

/-- The inverse ring homomorphism `Sym_R(M × R) ⟶ Γ(V, Sym^*(𝒞 ⊕ 𝒪_X))`. -/
def chartRingInv :
    SymmetricAlgebra Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) →+* (symAlg 𝒞).sectionRing V :=
  (AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))).symm.toRingHom.comp
    (SymPow.symAlgMap (sectionsSplit 𝒞 V).symm.toLinearMap).toRingHom

/-- Mapping symmetric algebras along a linear equivalence and then its inverse is the identity. -/
private theorem symAlgMap_symm_symAlgMap {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (x : SymmetricAlgebra R M) :
    SymPow.symAlgMap e.symm.toLinearMap (SymPow.symAlgMap e.toLinearMap x) = x := by
  rw [← AlgHom.comp_apply, ← SymPow.symAlgMap_comp,
    show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from LinearMap.ext e.symm_apply_apply,
    SymPow.symAlgMap_id, AlgHom.id_apply]

/-- `chartRingInv` is a left inverse of `chartRingHom`. -/
theorem chartRingInv_chartRingHom (x : (symAlg 𝒞).sectionRing V) :
    chartRingInv 𝒞 hV (chartRingHom 𝒞 hV x) = x := by
  simp only [chartRingHom, chartRingInv, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe]
  rw [symAlgMap_symm_symAlgMap, RingEquiv.symm_apply_apply]

/-- `chartRingInv` is a right inverse of `chartRingHom`. -/
theorem chartRingHom_chartRingInv (x : SymmetricAlgebra Γ(X, V) (Γ(𝒞, V) × Γ(X, V))) :
    chartRingHom 𝒞 hV (chartRingInv 𝒞 hV x) = x := by
  simp only [chartRingHom, chartRingInv, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe,
    RingEquiv.apply_symm_apply]
  simpa using symAlgMap_symm_symAlgMap (sectionsSplit 𝒞 V).symm x

/-- **The graded ring isomorphism `Γ(V, Sym^*(𝒞 ⊕ 𝒪_X)) ≅ Sym_R(M × R)`**, forward. -/
def chartGradedHom : (symAlg 𝒞).grading V →+*ᵍ
    (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) (Γ(𝒞, V) × Γ(X, V))) where
  toRingHom := chartRingHom 𝒞 hV
  map_mem {n x} hx := SymPow.symAlgMap_mapsTo n _ _
    ((AffinePieces.mem_symmetricPower_symSectionRingEquiv (module 𝒞) hV
      (bundlePieces (module 𝒞)) n x).2 hx)

/-- The graded ring isomorphism, backward. -/
def chartGradedInv :
    (fun n : ℕ => SymPow.symmetricPower n Γ(X, V) (Γ(𝒞, V) × Γ(X, V))) →+*ᵍ
      (symAlg 𝒞).grading V where
  toRingHom := chartRingInv 𝒞 hV
  map_mem {n x} hx := by
    refine (AffinePieces.mem_symmetricPower_symSectionRingEquiv (module 𝒞) hV
      (bundlePieces (module 𝒞)) n _).1 ?_
    change AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))
      ((AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))).symm
        (SymPow.symAlgMap (sectionsSplit 𝒞 V).symm.toLinearMap x)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact SymPow.symAlgMap_mapsTo n _ x hx

end Graded

/-- The restriction of `sectionT` to `V` is the unit of the summand `𝒪_X` over `V`. -/
theorem sectionT_restrict :
    (module 𝒞).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (sectionT 𝒞) =
      Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V 1) := by
  have h := PresheafOfModules.naturality_apply (inr 𝒞).val (homOfLE (le_top : V ≤ ⊤)).op
    (toUnitM ⊤ (1 : Γ(X, ⊤)))
  refine h.symm.trans (congrArg (fun a => Scheme.Modules.Hom.app (inr 𝒞) V a) ?_)
  exact map_one (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom

/-- The restriction of `sectionT` to `V` corresponds to the pair `(0, 1)`. -/
theorem sectionsSplit_sectionT :
    sectionsSplit 𝒞 V ((module 𝒞).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (sectionT 𝒞)) =
      (0, 1) := by
  rw [sectionT_restrict]
  exact (sectionsSplit 𝒞 V).apply_symm_apply (0, 1) |>.symm.trans
    (by rw [show (sectionsSplit 𝒞 V).symm (0, 1) =
      Scheme.Modules.Hom.app (inl 𝒞) V 0 + Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V 1)
      from rfl, map_zero, zero_add]) |>.symm

section Away

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] {V}
  (hV : IsAffineOpen V)

/-- `chartRingHom` sends `T` to the adjoined generator. -/
theorem chartRingHom_chartT :
    chartRingHom 𝒞 hV ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) =
      Stacks.SymAdjoinChart.adjoinedGen Γ(X, V) Γ(𝒞, V) := by
  show SymPow.symAlgMap (sectionsSplit 𝒞 V).toLinearMap
    (AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))
      (DirectSum.of ((symAlg 𝒞).sectionPieces V) 1
        ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
          ((module 𝒞).presheaf.map (homOfLE le_top).op (sectionT 𝒞))))) = _
  rw [AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen, SymPow.symAlgMap_ι,
    LinearEquiv.coe_coe, sectionsSplit_sectionT]
  rfl

/-- `chartRingInv` sends the adjoined generator to `T`. -/
theorem chartRingInv_adjoinedGen :
    chartRingInv 𝒞 hV (Stacks.SymAdjoinChart.adjoinedGen Γ(X, V) Γ(𝒞, V)) =
      ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) := by
  rw [← chartRingHom_chartT 𝒞 hV, chartRingInv_chartRingHom]

/-- A homogeneous localization is unchanged by mapping along a graded ring homomorphism and back
along a left inverse of it. -/
theorem _root_.HomogeneousLocalization.map_map_of_leftInverse {ι A B σ τ : Type*}
    [AddCommMonoid ι] [DecidableEq ι] [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
    [AddSubgroupClass σ A] [AddSubgroupClass τ B] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜]
    [GradedRing ℬ] {P : Submonoid A} {Q : Submonoid B} (g : 𝒜 →+*ᵍ ℬ) (g' : ℬ →+*ᵍ 𝒜)
    (hgg : ∀ a, g' (g a) = a) (hP : P ≤ Q.comap g) (hQ : Q ≤ P.comap g')
    (x : HomogeneousLocalization 𝒜 P) :
    HomogeneousLocalization.map g' hQ (HomogeneousLocalization.map g hP x) = x := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.map_mk]
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  congr 1
  · exact hgg _
  · exact Subtype.ext (hgg _)

/-- `chartGradedHom` maps the powers of `T` into the powers of the adjoined generator. -/
theorem powers_chartT_le_comap :
    Submonoid.powers ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) ≤
      (Submonoid.powers (Stacks.SymAdjoinChart.adjoinedGen Γ(X, V) Γ(𝒞, V))).comap
        (chartGradedHom 𝒞 hV) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  show _ = chartRingHom 𝒞 hV _
  rw [map_pow, chartRingHom_chartT]

/-- `chartGradedInv` maps the powers of the adjoined generator into the powers of `T`. -/
theorem powers_adjoinedGen_le_comap :
    Submonoid.powers (Stacks.SymAdjoinChart.adjoinedGen Γ(X, V) Γ(𝒞, V)) ≤
      (Submonoid.powers ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) :
        (symAlg 𝒞).sectionRing V)).comap (chartGradedInv 𝒞 hV) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  show _ = chartRingInv 𝒞 hV _
  rw [map_pow, chartRingInv_adjoinedGen]

/-- Mapping a fraction `x / f ^ n` along a graded ring homomorphism. -/
theorem _root_.HomogeneousLocalization.map_away_mk {ι A B σ τ : Type*}
    [AddCommMonoid ι] [DecidableEq ι] [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
    [AddSubgroupClass σ A] [AddSubgroupClass τ B] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜]
    [GradedRing ℬ] (g : 𝒜 →+*ᵍ ℬ) {f : A} {f' : B} (hff' : g f = f') {d : ι} (hf : f ∈ 𝒜 d)
    (hf' : f' ∈ ℬ d) (h : Submonoid.powers f ≤ (Submonoid.powers f').comap g) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    HomogeneousLocalization.map g h (HomogeneousLocalization.Away.mk 𝒜 hf n x hx) =
      HomogeneousLocalization.Away.mk ℬ hf' n (g x) (g.map_mem hx) := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk]
  congr 1
  exact Subtype.ext ((map_pow g f n).trans (by rw [hff']))

/-- **The degree-zero localization of `Γ(V, Sym^*(𝒞 ⊕ 𝒪_X))` at `T`, forward.** -/
def chartAwayHom :
    HomogeneousLocalization.Away ((symAlg 𝒞).grading V)
        ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) →+*
      Stacks.SymAdjoinChart.prodChartRing Γ(X, V) Γ(𝒞, V) :=
  HomogeneousLocalization.map (chartGradedHom 𝒞 hV) (powers_chartT_le_comap 𝒞 hV)

/-- The degree-zero localization at `T`, backward. -/
def chartAwayInv :
    Stacks.SymAdjoinChart.prodChartRing Γ(X, V) Γ(𝒞, V) →+*
      HomogeneousLocalization.Away ((symAlg 𝒞).grading V)
        ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) :=
  HomogeneousLocalization.map (chartGradedInv 𝒞 hV) (powers_adjoinedGen_le_comap 𝒞 hV)

/-- **The degree-zero localization of `Γ(V, Sym^*(𝒞)[T])` at `T` is `Sym_R(M)`.** -/
def chartAwayEquiv :
    HomogeneousLocalization.Away ((symAlg 𝒞).grading V)
        ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) ≃+*
      SymmetricAlgebra Γ(X, V) Γ(𝒞, V) :=
  (RingEquiv.ofRingHom (chartAwayHom 𝒞 hV) (chartAwayInv 𝒞 hV)
    (RingHom.ext fun x => HomogeneousLocalization.map_map_of_leftInverse _ _
      (chartRingHom_chartRingInv 𝒞 hV) (powers_adjoinedGen_le_comap 𝒞 hV)
      (powers_chartT_le_comap 𝒞 hV) x)
    (RingHom.ext fun x => HomogeneousLocalization.map_map_of_leftInverse _ _
      (chartRingInv_chartRingHom 𝒞 hV) (powers_chartT_le_comap 𝒞 hV)
      (powers_adjoinedGen_le_comap 𝒞 hV) x)).trans
    (Stacks.SymAdjoinChart.prodChartAlgEquiv Γ(X, V) Γ(𝒞, V)).symm.toRingEquiv

/-- The degree-one element of `Γ(V, Sym^*(𝒞)[T])` attached to a section `m` of `𝒞` over `V`. -/
def chartE (m : Γ(𝒞, V)) : (symAlg 𝒞).grading V 1 :=
  ⟨DirectSum.of ((symAlg 𝒞).sectionPieces V) 1
      ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
        (Scheme.Modules.Hom.app (inl 𝒞) V m)),
    (symAlg 𝒞).of_mem_grading V _⟩

/-- `chartRingInv` sends the generator `(m, 0)` of `Sym_R(M × R)` to `chartE m`. -/
theorem chartRingInv_ι (m : Γ(𝒞, V)) :
    chartRingInv 𝒞 hV (SymmetricAlgebra.ι Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) (m, 0)) =
      ((chartE 𝒞 m : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) := by
  show (AffinePieces.symSectionRingEquiv (module 𝒞) hV (bundlePieces (module 𝒞))).symm
    (SymPow.symAlgMap (sectionsSplit 𝒞 V).symm.toLinearMap
      (SymmetricAlgebra.ι Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) (m, 0))) = _
  rw [SymPow.symAlgMap_ι, RingEquiv.symm_apply_eq]
  refine Eq.trans ?_ (AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen (module 𝒞) hV
    (bundlePieces (module 𝒞)) (Scheme.Modules.Hom.app (inl 𝒞) V m)).symm
  congr 1
  show Scheme.Modules.Hom.app (inl 𝒞) V m + Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V 0) = _
  rw [show toUnitM V (0 : Γ(X, V)) = 0 from rfl, map_zero, add_zero]

/-- **The fraction `m / T` corresponds to the generator `m` of `Sym_R(M)`.** -/
theorem chartAwayEquiv_symm_ι (m : Γ(𝒞, V)) :
    (chartAwayEquiv 𝒞 hV).symm (SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m) =
      HomogeneousLocalization.Away.mk ((symAlg 𝒞).grading V) (chartT 𝒞 V).2 1
        ((chartE 𝒞 m : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V)
        (by simp) := by
  have hs : (chartAwayEquiv 𝒞 hV).symm (SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m) =
      chartAwayInv 𝒞 hV (Stacks.SymAdjoinChart.prodChartAlgEquiv Γ(X, V) Γ(𝒞, V)
        (SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m)) := rfl
  rw [hs, Stacks.SymAdjoinChart.prodChartAlgEquiv_apply, Stacks.SymAdjoinChart.toChart_ι]
  show HomogeneousLocalization.map (chartGradedInv 𝒞 hV) (powers_adjoinedGen_le_comap 𝒞 hV)
    (HomogeneousLocalization.Away.mk _ (Stacks.SymAdjoinChart.adjoinedGen_mem_one _ _) 1 _ _) = _
  rw [HomogeneousLocalization.map_away_mk (chartGradedInv 𝒞 hV) (chartRingInv_adjoinedGen 𝒞 hV)
    _ (chartT 𝒞 V).2]
  congr 1
  exact chartRingInv_ι 𝒞 hV m

end Away

end Stacks.Chow.ProjectiveCompletion
