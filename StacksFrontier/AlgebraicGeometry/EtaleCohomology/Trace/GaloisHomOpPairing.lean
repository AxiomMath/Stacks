module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisGlobalSectionsPairing
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpEvaluation
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantGlobalSections

/-!
# The Galois-equivariant evaluation pairing of `Γ^Gal(L)` with `Γ^Gal(ℋom^•_ℤ(L, K))`

Let `k` be a field, `K/k` separable algebraic, `Y` a quasi-compact quasi-separated `k`-scheme, `L`
a complex of sheaves of `Λ`-modules and `K` a complex of sheaves of abelian groups on `Y_étale`.
Evaluation `ev(a, e) = e_n(a)` is a section-wise pairing `L^n × ℋom^p_ℤ(L, K) ⟶ K^{p+n}`
(`Stacks.AbelianInternalHom.homOpEval`), hence induces a Galois-equivariant pairing on
`Γ^Gal = Γ(Y_K, -|_{Y_K})` (`Stacks.EtaleCohomology.galoisGlobalSectionsPairing`). With the Koszul
sign `(-1)^{np}` these assemble into a pairing of complexes of discrete modules
`Γ^Gal(L) × Γ^Gal(ℋom^•_ℤ(L, K)) ⟶ Γ^Gal(K)`, balanced along `Λ ≃ (Λᵐᵒᵖ)ᵐᵒᵖ`
(`Stacks.EtaleCohomology.galoisHomOpComplexPairing`), natural for precomposition
(`Stacks.EtaleCohomology.galoisHomOpComplexPairing_precomp`).

This is the chain-level Poincaré pairing of Tag 03VM before the trace: `L` an injective
resolution of `j_! ℱ_M` on the compactification, `K` one of `j_! μ_n`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius Stacks.AbelianInternalHom

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

section Linear

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
  {Λ₁ Λ₂ Λ₃ : Type} [Ring Λ₁] [Ring Λ₂] [Ring Λ₃] {G₁ : EtaleModules.{u, 0} Λ₁ Y.left}
  {G₂ : EtaleModules.{u, 0} Λ₂ Y.left} {G₃ : EtaleModules.{u, 0} Λ₃ Y.left}

/-- **The Galois pairing is compatible with linear combinations of section-wise pairings.** -/
theorem galoisGlobalSectionsPairing_eq_units_smul_sub (b b₁ b₂ : EtaleSectionPairing G₁ G₂ G₃)
    (ε : ℤˣ) (hb : ∀ (U : Y.left.Etaleᵒᵖ) (a : G₁.obj.obj U) (c : G₂.obj.obj U),
      b.app U a c = ε • (b₁.app U a c - b₂.app U a c))
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairing Y K b z₁ z₂ =
      ε • (galoisGlobalSectionsPairing Y K b₁ z₁ z₂ -
        galoisGlobalSectionsPairing Y K b₂ z₁ z₂) := by
  obtain ⟨i, -, a₁, a₂, h₁, h₂⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ ⊥
  apply ΓRes_etaleMkId_injective
  let fs : G₃.obj.obj (op ((fieldStageSystem Y K).obj (op i))) →+ _ :=
    AddMonoidHom.mk' (fieldStageSection Λ₃ Y K G₃ i) (fieldStageSection_add Λ₃ Y K G₃ i)
  rw [Units.smul_def, map_zsmul, map_sub, ΓRes_galoisGlobalSectionsPairing Y K b h₁ h₂,
    ΓRes_galoisGlobalSectionsPairing Y K b₁ h₁ h₂, ΓRes_galoisGlobalSectionsPairing Y K b₂ h₁ h₂,
    hb, Units.smul_def]
  exact (map_zsmul fs _ _).trans (congrArg _ (map_sub fs _ _))


omit [Algebra.IsSeparable k K] [QuasiCompact Y.hom] [QuasiSeparated Y.hom] in
/-- Section-wise pairings are determined by their values. -/
lemma EtaleSectionPairing.ext' {b b' : EtaleSectionPairing G₁ G₂ G₃}
    (h : ∀ (U : Y.left.Etaleᵒᵖ) (a : G₁.obj.obj U) (c : G₂.obj.obj U), b.app U a c = b'.app U a c) :
    b = b' := by
  obtain ⟨app, nat⟩ := b
  obtain ⟨app', nat'⟩ := b'
  obtain rfl : app = app' := funext fun U => AddMonoidHom.ext fun a => AddMonoidHom.ext fun c =>
    h U a c
  rfl

/-- A section-wise pairing precomposed with morphisms of sheaves in its two arguments. -/
def EtaleSectionPairing.precomp (b : EtaleSectionPairing G₁ G₂ G₃)
    {G₁' : EtaleModules.{u, 0} Λ₁ Y.left} {G₂' : EtaleModules.{u, 0} Λ₂ Y.left}
    (v₁ : G₁' ⟶ G₁) (v₂ : G₂' ⟶ G₂) : EtaleSectionPairing G₁' G₂' G₃ where
  app U := (b.app U).compl₂ (v₂.hom.app U).hom.toAddMonoidHom |>.comp
    (v₁.hom.app U).hom.toAddMonoidHom
  naturality f a c := by
    change G₃.obj.map f (b.app _ (v₁.hom.app _ a) (v₂.hom.app _ c)) =
      b.app _ (v₁.hom.app _ (G₁'.obj.map f a)) (v₂.hom.app _ (G₂'.obj.map f c))
    rw [b.naturality, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← v₁.hom.naturality, ← v₂.hom.naturality]
    rfl

/-- A section-wise pairing postcomposed with a morphism of sheaves. -/
def EtaleSectionPairing.postcomp (b : EtaleSectionPairing G₁ G₂ G₃)
    {G₃' : EtaleModules.{u, 0} Λ₃ Y.left} (v₃ : G₃ ⟶ G₃') : EtaleSectionPairing G₁ G₂ G₃' where
  app U := (b.app U).compr₂ (v₃.hom.app U).hom.toAddMonoidHom
  naturality f a c := by
    change G₃'.obj.map f (v₃.hom.app _ (b.app _ a c)) =
      v₃.hom.app _ (b.app _ (G₁.obj.map f a) (G₂.obj.map f c))
    rw [← b.naturality, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      v₃.hom.naturality]

/-- **`Γ^Gal` of a precomposed pairing.** -/
theorem galoisGlobalSectionsPairing_precomp (b : EtaleSectionPairing G₁ G₂ G₃)
    {G₁' : EtaleModules.{u, 0} Λ₁ Y.left} {G₂' : EtaleModules.{u, 0} Λ₂ Y.left}
    (v₁ : G₁' ⟶ G₁) (v₂ : G₂' ⟶ G₂)
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁'))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂')) :
    galoisGlobalSectionsPairing Y K (b.precomp Y v₁ v₂) z₁ z₂ =
      galoisGlobalSectionsPairing Y K b
        ((etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).map v₁) z₁)
        ((etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).map v₂) z₂) := by
  obtain ⟨i, -, a₁, a₂, h₁, h₂⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ ⊥
  apply ΓRes_etaleMkId_injective
  rw [ΓRes_galoisGlobalSectionsPairing Y K (b.precomp Y v₁ v₂) h₁ h₂,
    ΓRes_galoisGlobalSectionsPairing Y K b (ΓRes_map_eq_fieldStageSection Λ₁ Y K G₁' v₁ h₁)
      (ΓRes_map_eq_fieldStageSection Λ₂ Y K G₂' v₂ h₂)]
  rfl

/-- `Γ^Gal` of a pairing precomposed in the first argument only. -/
private theorem galoisGlobalSectionsPairing_precomp_left (b : EtaleSectionPairing G₁ G₂ G₃)
    {G₁' : EtaleModules.{u, 0} Λ₁ Y.left} (v₁ : G₁' ⟶ G₁)
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁'))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairing Y K (b.precomp Y v₁ (𝟙 _)) z₁ z₂ =
      galoisGlobalSectionsPairing Y K b
        ((etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).map v₁) z₁) z₂ := by
  have h := galoisGlobalSectionsPairing_precomp Y K b v₁ (𝟙 _) z₁ z₂
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
  exact h

/-- `Γ^Gal` of a pairing precomposed in the second argument only. -/
private theorem galoisGlobalSectionsPairing_precomp_right (b : EtaleSectionPairing G₁ G₂ G₃)
    {G₂' : EtaleModules.{u, 0} Λ₂ Y.left} (v₂ : G₂' ⟶ G₂)
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂')) :
    galoisGlobalSectionsPairing Y K (b.precomp Y (𝟙 _) v₂) z₁ z₂ =
      galoisGlobalSectionsPairing Y K b z₁
        ((etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).map
          ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).map v₂) z₂) := by
  have h := galoisGlobalSectionsPairing_precomp Y K b (𝟙 _) v₂ z₁ z₂
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
  exact h

/-- **`Γ^Gal` of a postcomposed pairing.** -/
theorem galoisGlobalSectionsPairing_postcomp (b : EtaleSectionPairing G₁ G₂ G₃)
    {G₃' : EtaleModules.{u, 0} Λ₃ Y.left} (v₃ : G₃ ⟶ G₃')
    (z₁ : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁))
    (z₂ : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisGlobalSectionsPairing Y K (b.postcomp Y v₃) z₁ z₂ =
      (etaleModuleGlobalSections.{u, 0} Λ₃ (fieldBaseChange Y K)).map
        ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).map v₃)
          (galoisGlobalSectionsPairing Y K b z₁ z₂) := by
  obtain ⟨i, -, a₁, a₂, h₁, h₂⟩ := exists_fieldStageSection_eq₂ Y K z₁ z₂ ⊥
  apply ΓRes_etaleMkId_injective
  rw [ΓRes_galoisGlobalSectionsPairing Y K (b.postcomp Y v₃) h₁ h₂,
    ΓRes_map_eq_fieldStageSection Λ₃ Y K G₃ v₃ (ΓRes_galoisGlobalSectionsPairing Y K b h₁ h₂)]
  rfl

end Linear

section Complex

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [Algebra.IsSeparable k kbar] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
  {Λ : Type} [Ring Λ] (L : CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ)
  (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Y.left) ℤ)

/-- The complex of abelian sheaves underlying a complex of sheaves of abelian groups. -/
abbrev etaleHomOpTarget :
    CochainComplex (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
  ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).mapHomologicalComplex
    _).obj Kc

/-- **The internal Hom complex `ℋom^•_ℤ(L, K)` on `Y_étale`**, a complex of sheaves of
`Λᵐᵒᵖ`-modules. -/
abbrev etaleHomOpComplex : CochainComplex (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left) ℤ :=
  homOpComplex Y.left.smallEtaleTopology L (etaleHomOpTarget Y Kc)

/-- **Evaluation `L^n × ℋom^p_ℤ(L, K) ⟶ K^q`, `p + n = q`, as a section-wise pairing.** -/
def etaleHomOpSectionPairing (n p q : ℤ) (h : p + n = q) :
    EtaleSectionPairing (L.X n) ((etaleHomOpComplex Y L Kc).X p) (Kc.X q) where
  app U := homOpEval Y.left.smallEtaleTopology L (etaleHomOpTarget Y Kc) n p q h U
  naturality f a c := homOpEval_naturality Y.left.smallEtaleTopology L (etaleHomOpTarget Y Kc)
    n p q h f a c

variable [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ]

/-- The Koszul sign `(-1)^{np}` of the pairing in bidegree `(n, p)`. -/
abbrev homOpPairingSign (n p : ℤ) : ℤˣ := (n * p).negOnePow

/-- The Koszul signs satisfy `(-1)^{(n+1)p} (-1)^{p+1} = (-1)^{n+1} (-1)^{n(p+1)}` and
`(-1)^{np} = -((-1)^{(n+1)p} (-1)^{p+1})`. -/
lemma homOpPairingSign_leibniz (n p : ℤ) :
    homOpPairingSign (n + 1) p * (p + 1).negOnePow =
      (n + 1).negOnePow * homOpPairingSign n (p + 1) ∧
    homOpPairingSign n p = -(homOpPairingSign (n + 1) p * (p + 1).negOnePow) := by
  unfold homOpPairingSign
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_succ]
  refine ⟨(Int.negOnePow_eq_iff _ _).2 ⟨p - n, by ring⟩,
    (Int.negOnePow_eq_iff _ _).2 ⟨-p - 1, by ring⟩⟩

/-- `Γ^Gal(L)` as a complex of discrete Galois modules. -/
abbrev galoisHomOpA : CochainComplex (GaloisModules Λ k kbar) ℤ :=
  ((galoisGlobalSections Λ Y kbar).mapHomologicalComplex _).obj L

/-- `Γ^Gal(ℋom^•_ℤ(L, K))` as a complex of discrete Galois modules over `Λᵐᵒᵖ`. -/
abbrev galoisHomOpE : CochainComplex (GaloisModules Λᵐᵒᵖ k kbar) ℤ :=
  ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex _).obj (etaleHomOpComplex Y L Kc)

/-- `Γ^Gal(K)` as a complex of discrete Galois modules over `ℤ`. -/
abbrev galoisHomOpG : CochainComplex (GaloisModules ℤ k kbar) ℤ :=
  ((galoisGlobalSections ℤ Y kbar).mapHomologicalComplex _).obj Kc

omit [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ] in
/-- For units `ε₀ ε' ε₁ ε u` of `ℤ` with `ε₀ ε' = u ε` and `ε₁ = -(ε₀ ε')`, and `x y` in an
additive commutative group, `ε₀ • ε' • (x - y) = ε₁ • y + u • ε • x`. -/
lemma homOpPairing_sign_algebra {G : Type*} [AddCommGroup G] (x y : G) (ε₀ ε' ε₁ ε u : ℤˣ)
    (h₁ : ε₀ * ε' = u * ε) (h₂ : ε₁ = -(ε₀ * ε')) :
    ε₀ • ε' • (x - y) = ε₁ • y + u • ε • x := by
  rw [smul_smul, smul_smul, h₂, ← h₁, smul_sub, Units.neg_smul]
  abel

/-- The components `(a, e) ↦ (-1)^{np} e_n(a)` of the Galois evaluation pairing. -/
def galoisHomOpPair (n p q : ℤ) (h : p + n = q) :
    ((galoisHomOpA Y kbar L).X n).obj.obj.V →+ ((galoisHomOpE Y kbar L Kc).X p).obj.obj.V →+
      ((galoisHomOpG Y kbar Kc).X q).obj.obj.V :=
  homOpPairingSign n p •
    galoisGlobalSectionsPairing Y kbar (etaleHomOpSectionPairing Y L Kc n p q h)

omit [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ] in
/-- The Galois evaluation pairing is Galois-equivariant: `⟨σ a, e⟩ = σ ⟨a, σ⁻¹ e⟩`. -/
lemma galoisHomOpPair_galois (n p q : ℤ) (h : p + n = q) (σ : kbar ≃ₐ[k] kbar)
    (a : ((galoisHomOpA Y kbar L).X n).obj.obj.V) (e : ((galoisHomOpE Y kbar L Kc).X p).obj.obj.V) :
    galoisHomOpPair Y kbar L Kc n p q h ((((galoisHomOpA Y kbar L).X n).obj.obj.ρ σ).hom a) e =
      (((galoisHomOpG Y kbar Kc).X q).obj.obj.ρ σ).hom (galoisHomOpPair Y kbar L Kc n p q h a
        ((((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ σ⁻¹).hom e)) := by
  have hinv : (((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ σ).hom
      ((((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ σ⁻¹).hom e) = e := by
    have h1 := (((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ).map_mul σ σ⁻¹
    rw [mul_inv_cancel, map_one] at h1
    exact (congrArg (fun φ => φ.hom e) h1).symm
  have key := galoisGlobalSectionsPairing_galoisAction Y kbar
    (etaleHomOpSectionPairing Y L Kc n p q h) σ a
    ((((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ σ⁻¹).hom e)
  conv_lhs => rw [← hinv]
  show homOpPairingSign n p • galoisGlobalSectionsPairing Y kbar
      (etaleHomOpSectionPairing Y L Kc n p q h)
        ((((galoisHomOpA Y kbar L).X n).obj.obj.ρ σ).hom a)
        ((((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ σ).hom
          ((((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ σ⁻¹).hom e)) =
    (((galoisHomOpG Y kbar Kc).X q).obj.obj.ρ σ).hom (homOpPairingSign n p •
      galoisGlobalSectionsPairing Y kbar (etaleHomOpSectionPairing Y L Kc n p q h) a
        ((((galoisHomOpE Y kbar L Kc).X p).obj.obj.ρ σ⁻¹).hom e))
  refine (congrArg (homOpPairingSign n p • ·) key).trans ?_
  rw [Units.smul_def, Units.smul_def]
  exact (map_zsmul _ _ _).symm

omit [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ] in
/-- The Galois evaluation pairing is balanced: `⟨r a, e⟩ = ⟨a, r e⟩` for `r : Λ` acting on
`Γ^Gal(ℋom^•_ℤ(L, K))` through `Λ ≃ (Λᵐᵒᵖ)ᵐᵒᵖ`. -/
lemma galoisHomOpPair_balanced (n p q : ℤ) (h : p + n = q) (r : Λ)
    (a : ((galoisHomOpA Y kbar L).X n).obj.obj.V) (e : ((galoisHomOpE Y kbar L Kc).X p).obj.obj.V) :
    galoisHomOpPair Y kbar L Kc n p q h (r • a) e =
      galoisHomOpPair Y kbar L Kc n p q h a (((RingEquiv.opOp Λ).toRingHom r).unop • e) := by
    show homOpPairingSign n p • galoisGlobalSectionsPairing Y kbar _ (r • a) e =
      homOpPairingSign n p • galoisGlobalSectionsPairing Y kbar _ a (MulOpposite.op r • e)
    exact congrArg (homOpPairingSign n p • ·)
      (galoisGlobalSectionsPairing_smul_left_eq_smul_right Y kbar _ r (MulOpposite.op r)
        (fun U a c => homOpEval_smul _ L (etaleHomOpTarget Y Kc) n p q h U r a c) a e)

omit [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ] in
/-- **The Leibniz rule for the Galois evaluation pairing**:
`⟨d a, e⟩ = d ⟨a, e⟩ + (-1)^{n+1} ⟨a, d e⟩` for `a` of degree `n`. -/
lemma galoisHomOpPair_leibniz (n p q q' : ℤ) (h : p + n = q) (hq : q + 1 = q')
    (a : ((galoisHomOpA Y kbar L).X n).obj.obj.V) (e : ((galoisHomOpE Y kbar L Kc).X p).obj.obj.V) :
    galoisHomOpPair Y kbar L Kc (n + 1) p q' (by omega)
        (((galoisHomOpA Y kbar L).d n (n + 1)).hom.hom.hom.hom a) e =
      (((galoisHomOpG Y kbar Kc).d q q').hom.hom.hom.hom
          (galoisHomOpPair Y kbar L Kc n p q h a e)) +
        (n + 1).negOnePow • galoisHomOpPair Y kbar L Kc n (p + 1) q' (by omega) a
          (((galoisHomOpE Y kbar L Kc).d p (p + 1)).hom.hom.hom.hom e) := by
    obtain rfl : q = q' - 1 := by omega
    let δ := (etaleHomOpComplex Y L Kc).d p (p + 1)
    have hb : ∀ (U : Y.left.Etaleᵒᵖ) (a : (L.X n).obj.obj U)
        (c : ((etaleHomOpComplex Y L Kc).X p).obj.obj U),
        ((etaleHomOpSectionPairing Y L Kc (n + 1) p q' (by omega)).precomp Y (L.d n (n + 1))
          (𝟙 _)).app U a c =
        (p + 1).negOnePow • ((((etaleHomOpSectionPairing Y L Kc n (p + 1) q' (by omega)).precomp Y
          (𝟙 _) δ).app U a c : (Kc.X q').obj.obj U) -
            (((etaleHomOpSectionPairing Y L Kc n p (q' - 1) h).postcomp Y
              (Kc.d (q' - 1) q')).app U a c : (Kc.X q').obj.obj U)) := by
      intro U a c
      have hd : (etaleHomOpSectionPairing Y L Kc n (p + 1) q' (by omega)).app U a
          ((δ.hom.app U).hom c) =
        ((Kc.d (q' - 1) q').hom.app U).hom
            ((etaleHomOpSectionPairing Y L Kc n p (q' - 1) h).app U a c) +
          (p + 1).negOnePow • (etaleHomOpSectionPairing Y L Kc (n + 1) p q' (by omega)).app U
            (((L.d n (n + 1)).hom.app U).hom a) c := by
        have hδ : δ = homOpComplexD _ L (etaleHomOpTarget Y Kc) p := homOpComplex_d _ _ _ p
        rw [hδ]
        exact homOpEval_d _ L (etaleHomOpTarget Y Kc) n p q' (by omega) U a c
      show (etaleHomOpSectionPairing Y L Kc (n + 1) p q' (by omega)).app U
          (((L.d n (n + 1)).hom.app U).hom a) c =
        (p + 1).negOnePow • ((etaleHomOpSectionPairing Y L Kc n (p + 1) q' (by omega)).app U a
          ((δ.hom.app U).hom c) - ((Kc.d (q' - 1) q').hom.app U).hom
            ((etaleHomOpSectionPairing Y L Kc n p (q' - 1) h).app U a c))
      rw [hd, add_sub_cancel_left, smul_smul, Int.units_mul_self, one_smul]
    have hB := galoisGlobalSectionsPairing_eq_units_smul_sub Y kbar _ _ _ _ hb a e
    have hA := galoisGlobalSectionsPairing_precomp_left Y kbar
      (etaleHomOpSectionPairing Y L Kc (n + 1) p q' (by omega)) (L.d n (n + 1)) a e
    have hC := galoisGlobalSectionsPairing_precomp_right Y kbar
      (etaleHomOpSectionPairing Y L Kc n (p + 1) q' (by omega)) δ a e
    have hD := galoisGlobalSectionsPairing_postcomp Y kbar
      (etaleHomOpSectionPairing Y L Kc n p (q' - 1) h) (Kc.d (q' - 1) q') a e
    have key := hA.symm.trans (hB.trans (congrArg ((p + 1).negOnePow • ·)
      (congrArg₂ (· - ·) hC hD)))
    obtain ⟨hs₁, hs₂⟩ := homOpPairingSign_leibniz n p
    show homOpPairingSign (n + 1) p • galoisGlobalSectionsPairing Y kbar
        (etaleHomOpSectionPairing Y L Kc (n + 1) p q' (by omega))
          ((etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).map
            ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map
              (L.d n (n + 1))) a) e =
      (etaleModuleGlobalSections.{u, 0} ℤ (fieldBaseChange Y kbar)).map
          ((etaleModuleInverseImage.{u, 0} ℤ (fieldBaseChangeProj Y kbar)).map (Kc.d (q' - 1) q'))
        (homOpPairingSign n p • galoisGlobalSectionsPairing Y kbar
          (etaleHomOpSectionPairing Y L Kc n p (q' - 1) h) a e) +
      (n + 1).negOnePow • (homOpPairingSign n (p + 1) • galoisGlobalSectionsPairing Y kbar
        (etaleHomOpSectionPairing Y L Kc n (p + 1) q' (by omega)) a
          ((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar)).map
            ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj Y kbar)).map δ) e))
    refine (congrArg (homOpPairingSign (n + 1) p • ·) key).trans ?_
    refine (homOpPairing_sign_algebra _ _ _ _ _ _ _ hs₁ hs₂).trans ?_
    congr 1
    rw [Units.smul_def, Units.smul_def]
    exact (map_zsmul _ _ _).symm


/-- **The Galois-equivariant evaluation pairing of complexes**
`Γ^Gal(L)^n × Γ^Gal(ℋom^•_ℤ(L, K))^p ⟶ Γ^Gal(K)^{p+n}`, `(a, e) ↦ (-1)^{np} e_n(a)`, balanced along
`Λ ≃ (Λᵐᵒᵖ)ᵐᵒᵖ`. -/
def galoisHomOpComplexPairing :
    Stacks.ContinuousCohomology.ComplexPairing Λᵐᵒᵖ (RingEquiv.opOp Λ).toRingHom
      (galoisHomOpA Y kbar L) (galoisHomOpE Y kbar L Kc) (galoisHomOpG Y kbar Kc) where
  pair := galoisHomOpPair Y kbar L Kc
  galois := galoisHomOpPair_galois Y kbar L Kc
  balanced := galoisHomOpPair_balanced Y kbar L Kc
  leibniz := galoisHomOpPair_leibniz Y kbar L Kc

variable {L} in
omit [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ] in
/-- **The Galois evaluation pairing is natural for precomposition**:
`⟨Γ(φ) a, e⟩ = ⟨a, Γ(φ^*) e⟩` for a morphism of complexes `φ : L' ⟶ L`. -/
lemma galoisHomOpPair_precomp {L' : CochainComplex (EtaleModules.{u, 0} Λ Y.left) ℤ} (φ : L' ⟶ L)
    (n p q : ℤ) (h : p + n = q) (a : ((galoisHomOpA Y kbar L').X n).obj.obj.V)
    (e : ((galoisHomOpE Y kbar L Kc).X p).obj.obj.V) :
    galoisHomOpPair Y kbar L Kc n p q h
        ((((galoisGlobalSections Λ Y kbar).mapHomologicalComplex _).map φ).f n |>.hom.hom.hom.hom a)
        e =
      galoisHomOpPair Y kbar L' Kc n p q h a
        ((((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex _).map
          (homOpComplexPrecomp (M := etaleHomOpTarget Y Kc) φ)).f p |>.hom.hom.hom.hom e) := by
  have h1 := galoisGlobalSectionsPairing_precomp_left Y kbar
    (etaleHomOpSectionPairing Y L Kc n p q h) (φ.f n) a e
  have h2 := galoisGlobalSectionsPairing_precomp_right Y kbar
    (etaleHomOpSectionPairing Y L' Kc n p q h)
      ((homOpComplexPrecomp (M := etaleHomOpTarget Y Kc) φ).f p) a e
  have hsame : (etaleHomOpSectionPairing Y L Kc n p q h).precomp Y (φ.f n) (𝟙 _) =
      (etaleHomOpSectionPairing Y L' Kc n p q h).precomp Y (𝟙 _)
        ((homOpComplexPrecomp (M := etaleHomOpTarget Y Kc) φ).f p) :=
    EtaleSectionPairing.ext' Y fun U a c =>
      homOpEval_precomp _ L (etaleHomOpTarget Y Kc) φ n p q h U a c
  have key := h1.symm.trans
    ((congrArg (fun b => galoisGlobalSectionsPairing Y kbar b a e) hsame).trans h2)
  exact congrArg (homOpPairingSign n p • ·) key

end Complex

end Stacks.EtaleCohomology

end
