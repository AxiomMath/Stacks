module

public import StacksFrontier.AlgebraicGeometry.ProEtale.BoundedLocallyConstantReduction
public import StacksFrontier.AlgebraicGeometry.ProEtale.CoefficientRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantCovering
import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantClopenPieces
import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantDerivedCompletion
import StacksFrontier.AlgebraicGeometry.ProEtale.AdicModelReductionSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantSheafMaps
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicQuotientTower
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSectionsCriterion
import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Linear
import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TopDegree

/-!
# Sheaves with constant reduction are completed constant sheaves

Let `U` be a scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. This file proves the case
`a = b` of the induction in the proof of Stacks 09C3: a derived complete sheaf `F` of
`Λ`-modules on `U_proét` with `Tor₁(F, \underline{N}) = 0` for every `Λ`-module `N` killed by
`I`, whose reduction `F ⊗ \underline{Λ/I}` is the constant sheaf of a finite module `M̄` and is
reached by the global sections of `F`, is the completed constant sheaf `\underline{M}^∧` of a
finite projective `Λ^∧`-module `M`.

The source's argument is followed. On a nonempty `U`, `M̄` is flat over `Λ/I`, since tensoring
the constant sheaves of an injection of modules killed by `I` with `F` stays injective; it is
then finite projective and lifts to a finite projective `Λ^∧`-module `M`. Lifting generators of
`M̄` to global sections of `F` and splitting `(Λ^∧)^r → M` gives a map `\underline{M}^∧ → F`
which is an isomorphism modulo `I`. Its cokernel and kernel are derived complete and vanish
modulo `I` (for the kernel by the vanishing of `Tor₁`), hence vanish (Stacks 09BY).

## Main definitions

* `AlgebraicGeometry.ProEtale.reductionMap`: the reduction `G → \underline{Λ/I} ⊗ G`.
* `AlgebraicGeometry.ProEtale.completedConstantSheafFunctor` and
  `AlgebraicGeometry.ProEtale.completedConstantSheafNatTrans`: `M ↦ \underline{M}^∧` and the
  natural maps `\underline{M} → \underline{M}^∧`.

## Main results

* `AlgebraicGeometry.ProEtale.isQuotientBy_reductionMap`: `G → \underline{Λ/I} ⊗ G` is the
  quotient of `G` by `I`.
* `AlgebraicGeometry.ProEtale.mono_whiskerLeft_of_isZero_homology`: `Tor₁`-vanishing makes
  tensoring a short exact sequence left exact.
* `AlgebraicGeometry.ProEtale.isZero_of_isDerivedComplete_of_isZero_tensor`: Nakayama for
  derived complete sheaves.
* `AlgebraicGeometry.ProEtale.isIso_whiskerLeft_completedConstantSheafUnit_of_projective`: the
  reduction of `\underline{M} → \underline{M}^∧` is an isomorphism for `M` finite projective over
  `Λ^∧`.
* `AlgebraicGeometry.ProEtale.isIso_of_isIso_whiskerLeft_quotientConstantSheaf`: a map of
  derived complete sheaves which is an isomorphism modulo `I` is an isomorphism.
* `AlgebraicGeometry.ProEtale.exists_iso_completedConstantSheaf_of_reduction_iso`: the base case
  of Stacks 09C3.

## References

* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
* [Stacks Project, Tag 09BY](https://stacks.math.columbia.edu/tag/09BY)
* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w v


section QuotientFlat

variable {R : Type v} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
  [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M]

/-- Over a quotient ring, scalars move across the tensor product over the base ring. -/
theorem TensorProduct.compatibleSMul_quotient (N : Type*) [AddCommGroup N] [Module R N]
    [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    TensorProduct.CompatibleSMul R (R ⧸ I) M N := by
  refine ⟨fun a m n => ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, TensorProduct.smul_tmul]

/-- **Flatness over a quotient ring from the base ring.** A module `M` over `R/I` is flat as soon
as `M ⊗_R J → M ⊗_R R/I` is injective for every ideal `J` of `R/I`: the tensor products over `R`
and over `R/I` of two `R/I`-modules agree. -/
theorem Module.Flat.quotient_of_lTensor_injective
    (h : ∀ J : Ideal (R ⧸ I), Function.Injective ((J.subtype.restrictScalars R).lTensor M)) :
    Module.Flat (R ⧸ I) M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  have := TensorProduct.compatibleSMul_quotient I M J
  have := TensorProduct.compatibleSMul_quotient I M (R ⧸ I)
  let e₁ := TensorProduct.equivOfCompatibleSMul R (R ⧸ I) R M J
  let e₂ := TensorProduct.equivOfCompatibleSMul R (R ⧸ I) R M (R ⧸ I)
  have hcomm : ∀ x, e₂ (J.subtype.lTensor M x) =
      (J.subtype.restrictScalars R).lTensor M (e₁ x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m j => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply e₁.injective
  apply h J
  rw [← hcomm, ← hcomm, hxy]

end QuotientFlat


section NatTransIso

variable {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)

/-- A component of a natural transformation at a retract of an object where it is an
isomorphism is an isomorphism. -/
theorem CategoryTheory.NatTrans.isIso_app_of_retract {A B : C} (s : A ⟶ B) (p : B ⟶ A)
    (hsp : s ≫ p = 𝟙 A) (hB : IsIso (α.app B)) : IsIso (α.app A) := by
  refine ⟨G.map s ≫ inv (α.app B) ≫ F.map p, ?_, ?_⟩
  · rw [← Category.assoc, ← α.naturality, Category.assoc, IsIso.hom_inv_id_assoc, ← F.map_comp,
      hsp, F.map_id]
  · rw [Category.assoc, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc, ← G.map_comp, hsp,
      G.map_id]

/-- A component of a natural transformation between additive functors at a finite biproduct of
objects where it is an isomorphism is an isomorphism. -/
theorem CategoryTheory.NatTrans.isIso_app_biproduct_of_finite [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D] [F.Additive] [G.Additive] {J : Type}
    [Finite J] (f : J → C) (hf : ∀ j, IsIso (α.app (f j))) : IsIso (α.app (⨁ f)) := by
  have := Fintype.ofFinite J
  refine ⟨∑ j, G.map (biproduct.π f j) ≫ inv (α.app (f j)) ≫ F.map (biproduct.ι f j), ?_, ?_⟩
  · simp only [Preadditive.comp_sum, ← α.naturality_assoc, IsIso.hom_inv_id_assoc,
      ← F.map_comp, ← F.map_sum, biproduct.total, F.map_id]
  · simp only [Preadditive.sum_comp, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc,
      ← G.map_comp, ← G.map_sum, biproduct.total, G.map_id]

/-- In a commutative square whose other three sides are isomorphisms, the fourth is one. -/
theorem CategoryTheory.isIso_of_comm_sq {A B A' B' : C} {f : A ⟶ B} {a : A ⟶ A'} {b : B ⟶ B'}
    {g : A' ⟶ B'} (h : a ≫ g = f ≫ b) (ha : IsIso a) (hf : IsIso f) (hb : IsIso b) : IsIso g := by
  rw [show g = inv a ≫ f ≫ b by rw [← h, IsIso.inv_hom_id_assoc]]
  infer_instance

end NatTransIso

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Sheaf.symmetricCategory Stacks.ModuleSheaf.monoidalClosed
  Stacks.ModuleSheaf.derivedMonoidal Stacks.ModuleSheaf.derivedSymmetric

section Reduction

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ] (I : Ideal Λ)

/-- The quotient map `\underline{Λ} → \underline{Λ/I}` of constant sheaves on `X_proét`. -/
abbrev constantQuotientMap :
    𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ⟶
      quotientConstantSheaf X Λ I :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ I).toLinearMap)

/-- The reduction `G → \underline{Λ/I} ⊗ G` of a sheaf of `Λ`-modules modulo `I`. -/
def reductionMap (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :
    G ⟶ quotientConstantSheaf X Λ I ⊗ G :=
  (λ_ G).inv ≫ constantQuotientMap I ▷ G

/-- The reduction map is natural. -/
@[reassoc]
theorem reductionMap_naturality
    {G H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)} (f : G ⟶ H) :
    reductionMap I G ≫ quotientConstantSheaf X Λ I ◁ f = f ≫ reductionMap I H := by
  simp only [reductionMap, Category.assoc, ← whisker_exchange, leftUnitor_inv_naturality_assoc]

/-- `\underline{Λ} → \underline{Λ/I}` is an epimorphism. -/
instance epi_constantQuotientMap : Epi (constantQuotientMap (X := X) I) := by
  have : Epi (show ModuleCat.of Λ Λ ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)) from
        ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ I).toLinearMap) :=
    ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  exact (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map_epi _

/-- The reduction map is an epimorphism. -/
instance epi_reductionMap (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :
    Epi (reductionMap I G) := by
  unfold reductionMap
  have : Epi (constantQuotientMap (X := X) I ▷ G) :=
    (tensorRight G).map_epi (constantQuotientMap I)
  infer_instance

/-- The constant sheaf functor on `X_proét` is `Λ`-linear. -/
instance linear_constantSheaf :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).Linear Λ :=
  inferInstanceAs (Functor.Linear Λ (Functor.const _ ⋙
    presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))

/-- Multiplication by an element of `I` on `\underline{Λ}`, tensored with a sheaf killed by `I`,
vanishes. -/
theorem smul_whiskerRight_eq_zero
    {A : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (φ : A ⟶ 𝟙_ _) {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    {a : Λ} (ha : a • 𝟙 H = 0) : (a • φ) ▷ H = 0 := by
  rw [show a • φ = φ ≫ (a • 𝟙 _) by rw [Linear.comp_smul, Category.comp_id], comp_whiskerRight]
  refine (congrArg (φ ▷ H ≫ ·) ((Stacks.ModuleSheaf.smul_id_whiskerRight a _ H).trans
    (Stacks.ModuleSheaf.whiskerLeft_smul_id a _ H).symm)).trans ?_
  simp only [ha, MonoidalPreadditive.whiskerLeft_zero, comp_zero]

/-- `I` kills `Λ/I`, read as a `Λ`-module. -/
private theorem smul_eq_zero_quotient {R : Type v} [CommRing R] (I : Ideal R) (a : R)
    (ha : a ∈ I) (b : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (R ⧸ I) (R ⧸ I))) : a • b = 0 := by
  change (Ideal.Quotient.mk I a * (show R ⧸ I from b) : R ⧸ I) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]

variable [IsNoetherianRing Λ]

/-- **A sheaf killed by `I` is its own reduction modulo `I`.** If `a • 𝟙 H = 0` for every
`a ∈ I`, then `H → \underline{Λ/I} ⊗ H` is an isomorphism: `\underline{I} ⊗ H → H` vanishes, as
`\underline{I}` is a quotient of `\underline{Λ}^k` through multiplication by generators of `I`, and
`\underline{I} → \underline{Λ} → \underline{Λ/I} → 0` stays exact after tensoring with `H`. -/
theorem isIso_reductionMap_of_smul_id_eq_zero
    {H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (hH : ∀ a ∈ I, a • 𝟙 H = 0) : IsIso (reductionMap I H) := by
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
  suffices IsIso (constantQuotientMap (X := X) I ▷ H) by unfold reductionMap; infer_instance
  let S : ShortComplex (ModuleCat.{max (u + 1) w} Λ) :=
    ShortComplex.mk (ModuleCat.ofHom I.subtype)
      (show ModuleCat.of Λ Λ ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)) from ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ I).toLinearMap)
      (by ext x; exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, Ideal.Quotient.eq_zero_iff_mem.1 hx⟩, rfl⟩
  have hg : Epi S.g := ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  let Φ := c ⋙ tensorRight H
  have hSΦ : (S.map Φ).Exact := hS.map_of_epi_of_preservesCokernel Φ hg inferInstance
  obtain ⟨k, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  let g : (Fin k → Λ) →ₗ[Λ] Λ := Fintype.linearCombination Λ a
  have hgI : ∀ f, g f ∈ I := fun f => by
    rw [← ha, ← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ f
  let g' : (Fin k → Λ) →ₗ[Λ] I := g.codRestrict I hgI
  have hg' : Function.Surjective g' := by
    rintro ⟨y, hy⟩
    rw [← ha, ← Fintype.range_linearCombination] at hy
    obtain ⟨f, rfl⟩ := hy
    exact ⟨f, rfl⟩
  have hfac : ModuleCat.ofHom g' ≫ S.f = ModuleCat.ofHom g := rfl
  have hsum : (ModuleCat.ofHom g : ModuleCat.of Λ (Fin k → Λ) ⟶ ModuleCat.of Λ Λ) =
      ∑ i, a i • ModuleCat.ofHom (LinearMap.proj i) := by
    ext f
    simp [g, Fintype.linearCombination_apply, mul_comm]
  have hzero' : c.map (ModuleCat.ofHom g) ▷ H = 0 := by
    rw [hsum, Functor.map_sum, sum_whiskerRight]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Functor.Linear.map_smul]
    exact smul_whiskerRight_eq_zero _ (hH (a i) (ha ▸ Submodule.subset_span ⟨i, rfl⟩))
  have hepi : Epi (c.map (ModuleCat.ofHom g') ▷ H) := by
    have : Epi (ModuleCat.ofHom g') := ConcreteCategory.epi_of_surjective _ hg'
    exact (c ⋙ tensorRight H).map_epi (ModuleCat.ofHom g')
  have hzero : (S.map Φ).f = 0 := by
    show c.map S.f ▷ H = 0
    rw [← cancel_epi (c.map (ModuleCat.ofHom g') ▷ H), ← comp_whiskerRight, ← Functor.map_comp,
      hfac, hzero', comp_zero]
  have : Mono (S.map Φ).g := hSΦ.mono_g hzero
  have : Epi (S.map Φ).g := Φ.map_epi S.g
  exact isIso_of_mono_of_epi (S.map Φ).g

omit [IsNoetherianRing Λ] in
/-- `\underline{Λ/I} ⊗ G` is killed by `I`. -/
theorem isAnnihilatedBy_quotientConstantSheaf_tensor
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :
    Stacks.ModuleSheaf.IsAnnihilatedBy (Scheme.ProEt.topology X) Λ I
      (quotientConstantSheaf X Λ I ⊗ G) := by
  have hQ := (Stacks.ModuleSheaf.isAnnihilatedBy_iff_smul_id _ _).1
    (Stacks.ModuleSheaf.isAnnihilatedBy_constantSheaf (Scheme.ProEt.topology X) Λ I
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)))
      (smul_eq_zero_quotient I))
  rw [Stacks.ModuleSheaf.isAnnihilatedBy_iff_smul_id]
  intro a ha
  refine (Stacks.ModuleSheaf.smul_id_whiskerRight a _ G).symm.trans ?_
  rw [hQ a ha, MonoidalPreadditive.zero_whiskerRight]

/-- **The reduction `G → \underline{Λ/I} ⊗ G` is the quotient of `G` by `I`.** -/
theorem isQuotientBy_reductionMap
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :
    Stacks.ModuleSheaf.IsQuotientBy (Scheme.ProEt.topology X) Λ I G
      (quotientConstantSheaf X Λ I ⊗ G) (reductionMap I G) := by
  refine ⟨isAnnihilatedBy_quotientConstantSheaf_tensor I G, fun H hH f => ?_⟩
  have := isIso_reductionMap_of_smul_id_eq_zero I
    ((Stacks.ModuleSheaf.isAnnihilatedBy_iff_smul_id _ _).1 hH)
  refine ⟨quotientConstantSheaf X Λ I ◁ f ≫ inv (reductionMap I H), ?_, fun g hg => ?_⟩
  · show reductionMap I G ≫ _ ≫ _ = f
    rw [reductionMap_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [← cancel_epi (reductionMap I G), hg, reductionMap_naturality_assoc, IsIso.hom_inv_id,
      Category.comp_id]

/-- **Comparing reductions through quotients by `I`.** If `qA : A → A'` and `qB : B → B'` are
quotients by `I` and `f : A → B` induces an isomorphism `A' → B'`, then the reduction
`\underline{Λ/I} ⊗ f` of `f` is an isomorphism. -/
theorem isIso_whiskerLeft_of_isQuotientBy
    {A B A' B' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)} (f : A ⟶ B)
    {qA : A ⟶ A'} {qB : B ⟶ B'}
    (hA : Stacks.ModuleSheaf.IsQuotientBy (Scheme.ProEt.topology X) Λ I A A' qA)
    (hB : Stacks.ModuleSheaf.IsQuotientBy (Scheme.ProEt.topology X) Λ I B B' qB)
    (f' : A' ⟶ B') (hf : qA ≫ f' = f ≫ qB) (hf' : IsIso f') :
    IsIso (quotientConstantSheaf X Λ I ◁ f) := by
  let κA := Stacks.ModuleSheaf.isQuotientByIso (isQuotientBy_reductionMap I A) hA
  let κB := Stacks.ModuleSheaf.isQuotientByIso (isQuotientBy_reductionMap I B) hB
  have hκA : reductionMap I A ≫ κA.hom = qA :=
    Stacks.ModuleSheaf.isQuotientByIso_hom_comp _ _
  have hκB : qB ≫ κB.inv = reductionMap I B := by
    rw [← Stacks.ModuleSheaf.isQuotientByIso_hom_comp (isQuotientBy_reductionMap I B) hB,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : quotientConstantSheaf X Λ I ◁ f = κA.hom ≫ f' ≫ κB.inv := by
    rw [← cancel_epi (reductionMap I A), reductionMap_naturality, reassoc_of% hκA,
      reassoc_of% hf, hκB]
  rw [this]
  infer_instance

end Reduction

section TorVanishing

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ]

/-- **Vanishing of `Tor₁` makes tensoring left exact.** Let `0 → S₁ → S₂ → S₃ → 0` be a short
exact sequence of sheaves of `Λ`-modules and `P` a sheaf with
`H⁻¹(P ⊗_Λ^L S₃) = 0`. Then `P ⊗ S₁ → P ⊗ S₂` is a monomorphism: it is `H⁰` of the first map of
the distinguished triangle `P ⊗^L S₁ → P ⊗^L S₂ → P ⊗^L S₃ →`, read through the top cohomology of
a derived tensor product with a sheaf placed in degree zero. -/
theorem mono_whiskerLeft_of_isZero_homology
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    {S : ShortComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
    (hS : S.ShortExact)
    (h : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
      ((DerivedCategory.singleFunctor _ 0).obj P ⊗ (DerivedCategory.singleFunctor _ 0).obj S.X₃))) :
    Mono (P ◁ S.f) := by
  let K := (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) 0).obj P
  obtain ⟨s, hs⟩ :=
    Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorLeft (Scheme.ProEt.topology X) Λ K
  let := s
  have hT := (tensorLeft K).map_distinguished _ hS.singleTriangle_distinguished
  have hmono : Mono ((DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft K ⋙
      DerivedCategory.homologyFunctor _ 0).map S.f) :=
    ((DerivedCategory.homologyFunctor _ 0).homologySequence_mono_shift_map_mor₁_iff _ hT (-1) 0
      (by omega)).2 (h.eq_of_src _ _)
  have : K.IsLE 0 := by dsimp only [K]; infer_instance
  obtain ⟨e⟩ := Stacks.ModuleSheaf.nonempty_homology_tensor_single_natIso_of_isLE
    (J := Scheme.ProEt.topology X) K 0
  have h₂ : Mono ((DerivedCategory.homologyFunctor _ 0).obj K ◁ S.f) := by
    have h' : (DerivedCategory.homologyFunctor _ 0).obj K ◁ S.f = (e.app S.X₁).symm.hom ≫
        (DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft K ⋙
          DerivedCategory.homologyFunctor _ 0).map S.f ≫ (e.app S.X₂).hom := by
      rw [Iso.app_hom, e.hom.naturality S.f, Iso.symm_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]
      rfl
    rw [h']
    exact inferInstance
  let i : (DerivedCategory.homologyFunctor _ 0).obj K ≅ P :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) 0).app P
  have h₃ : P ◁ S.f = (whiskerRightIso i.symm S.X₁).hom ≫
      (DerivedCategory.homologyFunctor _ 0).obj K ◁ S.f ≫ (whiskerRightIso i S.X₂).hom := by
    rw [whiskerRightIso_hom, whiskerRightIso_hom, Iso.symm_hom, ← whisker_exchange_assoc,
      ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
  rw [h₃]
  exact inferInstance

end TorVanishing

section Flatness

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ] (I : Ideal Λ)

/-- On a nonempty scheme, the constant sheaf functor reflects monomorphisms. -/
theorem mono_of_mono_constantSheaf_map [Nonempty X] {N N' : ModuleCat.{max (u + 1) w} Λ}
    (g : N ⟶ N')
    (hg : Mono ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map g)) :
    Mono g := by
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
  have : Mono (c.map (kernel.ι g)) := c.map_mono _
  have h₀ : c.map (kernel.ι g) = 0 := by
    rw [← cancel_mono (c.map g), ← c.map_comp, kernel.condition, c.map_zero, zero_comp]
  have h₁ : IsZero (c.obj (kernel g)) := by
    rw [h₀] at this
    exact IsZero.of_mono_zero _ (c.obj N)
  exact Preadditive.mono_of_isZero_kernel _ (isZero_of_isZero_constantSheaf _ h₁)

variable [IsNoetherianRing Λ]

attribute [local instance] Stacks.ModuleSheaf.constantSheafMonoidal in
/-- **`F ⊗ \underline{N}` through the reduction of `F`.** For a sheaf `N` killed by `I` and an
identification `F ⊗ \underline{Λ/I} ≅ \underline{M}`, the map `F ⊗ \underline{f}` induced by a map
`f : N' → N` of modules killed by `I` is, up to isomorphisms, the constant sheaf of
`M ⊗ f`. -/
theorem exists_iso_whiskerLeft_constantSheaf_map
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (Mbar : ModuleCat.{max (u + 1) w} Λ)
    (e : F ⊗ quotientConstantSheaf X Λ I ≅
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj Mbar)
    {N' N : ModuleCat.{max (u + 1) w} Λ} (f : N' ⟶ N)
    (hN' : ∀ x ∈ I, ∀ n : N', x • n = 0) (hN : ∀ x ∈ I, ∀ n : N, x • n = 0) :
    ∃ (i' : F ⊗ (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj N' ≅
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj (Mbar ⊗ N'))
      (i : F ⊗ (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj N ≅
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj (Mbar ⊗ N)),
      F ◁ (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map f ≫ i.hom =
        i'.hom ≫ (constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{max (u + 1) w} Λ)).map (Mbar ◁ f) := by
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
  have := isIso_reductionMap_of_smul_id_eq_zero I
    (fun a ha => smul_id_constantSheaf_eq_zero (Y := X) I hN' ha)
  have := isIso_reductionMap_of_smul_id_eq_zero I
    (fun a ha => smul_id_constantSheaf_eq_zero (Y := X) I hN ha)
  refine ⟨whiskerLeftIso F (asIso (reductionMap I (c.obj N'))) ≪≫
      (α_ F (quotientConstantSheaf X Λ I) (c.obj N')).symm ≪≫ whiskerRightIso e (c.obj N') ≪≫
      Functor.Monoidal.μIso c Mbar N',
    whiskerLeftIso F (asIso (reductionMap I (c.obj N))) ≪≫
      (α_ F (quotientConstantSheaf X Λ I) (c.obj N)).symm ≪≫ whiskerRightIso e (c.obj N) ≪≫
      Functor.Monoidal.μIso c Mbar N, ?_⟩
  simp only [Iso.trans_hom, whiskerLeftIso_hom, asIso_hom, Iso.symm_hom, whiskerRightIso_hom,
    Functor.Monoidal.μIso_hom]
  rw [Category.assoc, Category.assoc, Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
    ← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← reductionMap_naturality,
    MonoidalCategory.whiskerLeft_comp_assoc]

/-- **The reduction of `F` is flat when `Tor₁` vanishes.** Let `F` be a sheaf of `Λ`-modules on a
nonempty scheme with `H⁻¹(F ⊗_Λ^L \underline{N}) = 0` for every `Λ`-module `N` killed by `I`, and
with `F ⊗ \underline{Λ/I} ≅ \underline{M}` for a module `M` killed by `I`. Then for every
injection `f : N' → N` of modules killed by `I`, `M ⊗ f` is injective. -/
theorem injective_lTensor_of_isZero_homology [Nonempty X]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (htor : ∀ N : ModuleCat.{max (u + 1) w} Λ, (∀ x ∈ I, ∀ n : N, x • n = 0) →
      IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗ (DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj N))))
    (Mbar : ModuleCat.{max (u + 1) w} Λ)
    (e : F ⊗ quotientConstantSheaf X Λ I ≅
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj Mbar)
    {N' N : ModuleCat.{max (u + 1) w} Λ} (f : N' ⟶ N) (hf : Function.Injective f.hom)
    (hN : ∀ x ∈ I, ∀ n : N, x • n = 0) :
    Function.Injective (f.hom.lTensor Mbar) := by
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
  have hN' : ∀ x ∈ I, ∀ n : N', x • n = 0 := fun x hx n => hf (by
    rw [map_smul, hN x hx, map_zero])
  have : Mono f := (ModuleCat.mono_iff_injective f).2 hf
  let S₀ : ShortComplex (ModuleCat.{max (u + 1) w} Λ) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS₀ : S₀.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
  have hS := hS₀.map_of_exact c
  have hQ : ∀ x ∈ I, ∀ n : S₀.X₃, x • n = 0 := fun x hx n => by
    obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective (cokernel.π f)).1 inferInstance n
    rw [← map_smul, hN x hx, map_zero]
  have hmono : Mono (F ◁ c.map f) :=
    mono_whiskerLeft_of_isZero_homology F hS (htor _ hQ)
  obtain ⟨i', i, hi⟩ := exists_iso_whiskerLeft_constantSheaf_map I F Mbar e f hN' hN
  have : Mono (c.map (Mbar ◁ f)) := by
    rw [show c.map (Mbar ◁ f) = i'.inv ≫ F ◁ c.map f ≫ i.hom by rw [hi, Iso.inv_hom_id_assoc]]
    exact inferInstance
  exact (ModuleCat.mono_iff_injective _).1 (mono_of_mono_constantSheaf_map _ this)

end Flatness

section CompletedConstant

variable (X : Scheme.{u}) {Λ : Type (max (u + 1) w)} [CommRing Λ] (I : Ideal Λ)

/-- The completed constant sheaf `M ↦ \underline{M}^∧ = lim \underline{M/IⁿM}`, as a functor of the
coefficient module. -/
abbrev completedConstantSheafFunctor :
    ModuleCat.{max (u + 1) w} Λ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) :=
  adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I ⋙
    (Functor.whiskeringRight ℕᵒᵖ (ModuleCat.{max (u + 1) w} Λ)
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))).obj
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ⋙ lim

/-- The map `\underline{M} → \underline{M}^∧` induced by the quotient maps `M → M/IⁿM`. At `M = Λ`
this is `AlgebraicGeometry.ProEtale.completedConstantSheafMap`. -/
def completedConstantSheafUnit (M : ModuleCat.{max (u + 1) w} Λ) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj M ⟶
      (completedConstantSheafFunctor X I).obj M :=
  limit.lift _ ((constantSheaf (Scheme.ProEt.topology X)
    (ModuleCat.{max (u + 1) w} Λ)).mapCone (adicQuotientModuleCone I M))

/-- The components of `\underline{M} → \underline{M}^∧` are the constant quotient maps. -/
@[reassoc]
theorem completedConstantSheafUnit_π (M : ModuleCat.{max (u + 1) w} Λ) (n : ℕᵒᵖ) :
    completedConstantSheafUnit X I M ≫ limit.π _ n =
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map
        (ModuleCat.ofHom (I ^ n.unop • ⊤ : Submodule Λ M).mkQ) :=
  limit.lift_π _ _

/-- `\underline{M} → \underline{M}^∧` is natural in `M`. -/
@[reassoc]
theorem completedConstantSheafUnit_naturality {M N : ModuleCat.{max (u + 1) w} Λ} (f : M ⟶ N) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map f ≫
      completedConstantSheafUnit X I N =
      completedConstantSheafUnit X I M ≫ (completedConstantSheafFunctor X I).map f := by
  refine limit.hom_ext fun n => ?_
  rw [Category.assoc, completedConstantSheafUnit_π, Category.assoc]
  show _ = _ ≫ limMap _ ≫ _
  rw [limMap_π, ← Category.assoc, completedConstantSheafUnit_π]
  exact ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map_comp _
    _).symm.trans
      (((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).congr_map
      (ModuleCat.hom_ext (LinearMap.ext fun x => rfl))).trans
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map_comp
        (ModuleCat.ofHom (I ^ n.unop • ⊤ : Submodule Λ M).mkQ)
        (((adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I).map f).app n)))

/-- The maps `\underline{M} → \underline{M}^∧`, as a natural transformation. -/
@[simps]
def completedConstantSheafNatTrans :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) ⟶
      completedConstantSheafFunctor X I where
  app := completedConstantSheafUnit X I
  naturality _ _ f := completedConstantSheafUnit_naturality X I f

/-- At `M = Λ`, `\underline{M} → \underline{M}^∧` is `completedConstantSheafMap`. -/
theorem completedConstantSheafUnit_unitModule :
    completedConstantSheafUnit X I (Functor.unitModule Λ) = completedConstantSheafMap X I :=
  rfl

/-- The completed constant sheaf functor is additive. -/
instance completedConstantSheafFunctor_additive :
    (completedConstantSheafFunctor X I (Λ := Λ)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The reduction of `\underline{M} → \underline{M}^∧`, as a natural transformation. -/
abbrev completedConstantSheafNatTransReduction :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) ⋙
        tensorLeft (quotientConstantSheaf X Λ I) ⟶
      completedConstantSheafFunctor X I ⋙ tensorLeft (quotientConstantSheaf X Λ I) :=
  Functor.whiskerRight (completedConstantSheafNatTrans X I) _

variable {X I} [IsNoetherianRing Λ]

/-- The comparison `Λ → Λ^∧` induces an isomorphism of completed constant sheaves. -/
theorem isIso_completedConstantSheafFunctor_map_adicCompletionUnitHom :
    IsIso ((completedConstantSheafFunctor X I).map (adicCompletionUnitHom I)) := by
  dsimp only [completedConstantSheafFunctor, Functor.comp_map]
  infer_instance

/-- The comparison `Λ → Λ^∧` induces an isomorphism of the reductions of the constant sheaves. -/
theorem isIso_whiskerLeft_constantSheaf_map_adicCompletionUnitHom :
    IsIso (quotientConstantSheaf X Λ I ◁ (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)).map (adicCompletionUnitHom I)) := by
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
  let N := (restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj
    (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ))
  have hA := cast (congrArg (fun K => Stacks.ModuleSheaf.IsQuotientBy _ Λ K _ _ _) (pow_one I))
    (Stacks.ModuleSheaf.isQuotientBy_constantSheaf (Scheme.ProEt.topology X) Λ (I ^ 1)
      (Functor.unitModule Λ))
  have hB := cast (congrArg (fun K => Stacks.ModuleSheaf.IsQuotientBy _ Λ K _ _ _) (pow_one I))
    (Stacks.ModuleSheaf.isQuotientBy_constantSheaf (Scheme.ProEt.topology X) Λ (I ^ 1) N)
  let ū := ((adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I).map
      (adicCompletionUnitHom I)).app (op 1)
  have : IsIso ū := inferInstance
  have : IsIso (c.map ū) := Functor.map_isIso c ū
  refine isIso_whiskerLeft_of_isQuotientBy.{u, w} (X := X) I _ hA hB (c.map ū) ?_ this
  exact (c.map_comp _ _).symm.trans
    ((c.congr_map (ModuleCat.hom_ext (LinearMap.ext fun x => rfl))).trans
    (c.map_comp (adicCompletionUnitHom I) (ModuleCat.ofHom (I ^ 1 • ⊤ : Submodule Λ N).mkQ)))

/-- **The reduction of `\underline{Λ} → \underline{Λ}^∧` is an isomorphism.** -/
theorem isIso_whiskerLeft_completedConstantSheafUnit_unitModule :
    IsIso (quotientConstantSheaf X Λ I ◁
      completedConstantSheafUnit X I (Functor.unitModule Λ)) := by
  let Q := quotientConstantSheaf X Λ I
  let η := completedConstantSheafMap X I
  let D := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)
  let K := (DerivedCategory.singleFunctor D 0).obj Q
  have hQ : ∀ x ∈ I, x • 𝟙 Q = 0 := fun x hx => smul_id_constantSheaf_eq_zero (Y := X) I
    (smul_eq_zero_quotient I) hx
  have h₀ := isIso_whiskerRight_singleFunctor_zero_map_completedConstantSheafMap Q hQ
  have h₁ : IsIso ((tensorLeft K).map ((DerivedCategory.singleFunctor D 0).map η)) :=
    isIso_of_comm_sq (BraidedCategory.braiding_naturality_left _ _).symm inferInstance h₀
      inferInstance
  have : K.IsLE 0 := by dsimp only [K]; infer_instance
  obtain ⟨e⟩ := Stacks.ModuleSheaf.nonempty_homology_tensor_single_natIso_of_isLE
    (J := Scheme.ProEt.topology X) K 0
  have h₂ : IsIso ((DerivedCategory.homologyFunctor D 0).obj K ◁ η) :=
    isIso_of_comm_sq (e.hom.naturality η).symm inferInstance
      (Functor.map_isIso (DerivedCategory.homologyFunctor D 0) _) inferInstance
  let i : (DerivedCategory.homologyFunctor D 0).obj K ≅ Q :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).app Q
  exact isIso_of_comm_sq (whisker_exchange i.hom η).symm
    (inferInstanceAs (IsIso (whiskerRightIso i _).hom)) h₂
    (inferInstanceAs (IsIso (whiskerRightIso i _).hom))

/-- The reduction of `\underline{Λ^∧} → \underline{Λ^∧}^∧` is an isomorphism. -/
theorem isIso_whiskerLeft_completedConstantSheafUnit_adicCompletion :
    IsIso (quotientConstantSheaf X Λ I ◁ completedConstantSheafUnit X I
      ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj
        (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)))) := by
  refine isIso_of_comm_sq ?_
    (isIso_whiskerLeft_constantSheaf_map_adicCompletionUnitHom.{u, w} (X := X) (I := I))
    (isIso_whiskerLeft_completedConstantSheafUnit_unitModule.{u, w} (X := X) (I := I))
    (by
      have := isIso_completedConstantSheafFunctor_map_adicCompletionUnitHom.{u, w} (X := X) (I := I)
      exact Functor.map_isIso (tensorLeft (quotientConstantSheaf X Λ I))
        ((completedConstantSheafFunctor X I).map (adicCompletionUnitHom I)))
  rw [← MonoidalCategory.whiskerLeft_comp, completedConstantSheafUnit_naturality,
    MonoidalCategory.whiskerLeft_comp]
  rfl

/-- **The reduction of `\underline{M} → \underline{M}^∧` is an isomorphism for a finite projective
`Λ^∧`-module `M`.** It is a retract of `(Λ^∧)^r`, which is a finite direct sum of copies of
`Λ^∧`. -/
theorem isIso_whiskerLeft_completedConstantSheafUnit_of_projective
    (M : ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) [Module.Finite (AdicCompletion I Λ) M]
    [Module.Projective (AdicCompletion I Λ) M] :
    IsIso (quotientConstantSheaf X Λ I ◁ completedConstantSheafUnit X I
      ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj M)) := by
  let α := completedConstantSheafNatTransReduction X I (Λ := Λ)
  let ρ := restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I
  let A := ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)
  have hA : IsIso (α.app (ρ.obj A)) :=
    isIso_whiskerLeft_completedConstantSheafUnit_adicCompletion.{u, w} (X := X) (I := I)
  obtain ⟨r, p, hp⟩ := Module.Finite.exists_fin' (AdicCompletion I Λ) M
  obtain ⟨t, ht⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hsum : IsIso (α.app (⨁ fun _ : Fin r => ρ.obj A)) :=
    NatTrans.isIso_app_biproduct_of_finite α (fun _ : Fin r => ρ.obj A) (fun _ => hA)
  let e : ρ.obj (ModuleCat.of (AdicCompletion I Λ) (Fin r → AdicCompletion I Λ)) ≅
      ⨁ fun _ : Fin r => ρ.obj A :=
    ρ.mapIso (ModuleCat.biproductIsoPi fun _ : Fin r => A).symm ≪≫ ρ.mapBiproduct _
  have hR : IsIso (α.app (ρ.obj (ModuleCat.of (AdicCompletion I Λ)
      (Fin r → AdicCompletion I Λ)))) :=
    NatTrans.isIso_app_of_retract α e.hom e.inv e.hom_inv_id hsum
  exact NatTrans.isIso_app_of_retract α (ρ.map (ModuleCat.ofHom t)) (ρ.map (ModuleCat.ofHom p))
    (by rw [← ρ.map_comp, ← ModuleCat.ofHom_comp, ht, ModuleCat.ofHom_id, ρ.map_id]) hR

end CompletedConstant

section Nakayama

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ] (I : Ideal Λ)

attribute [local instance] SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  SheafOfModules.hasSheafify_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat

/-- If `\underline{Λ/I} ⊗ G = 0`, then `G ⊗_Λ Λ/I = 0` as a sheaf of `Λ/I`-modules: by the
projection formula, the latter, read over `Λ`, is `\underline{Λ/I} ⊗ G`. -/
theorem isZero_extendScalars_of_isZero_tensor
    {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (h : IsZero (quotientConstantSheaf X Λ I ⊗ G)) :
    IsZero ((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
      (Ideal.Quotient.mk I)).obj G) := by
  let P := (Stacks.ModuleSheaf.restrictScalarsTensorExtendScalarsIso (Scheme.ProEt.topology X)
    (Ideal.Quotient.mk I)).app
      (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I))), G)
  let r := (Stacks.ModuleSheaf.restrictScalarsConstantSheafIso (Scheme.ProEt.topology X)
    (Ideal.Quotient.mk I)).app (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I))
  have h₁ : IsZero ((Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X)
      (Ideal.Quotient.mk I)).obj (𝟙_ _ ⊗ (Stacks.ModuleSheaf.extendScalars
        (Scheme.ProEt.topology X) (Ideal.Quotient.mk I)).obj G)) :=
    h.of_iso (P ≪≫ whiskerRightIso r G)
  exact (Stacks.ModuleSheaf.isZero_of_isZero_restrictScalars_obj _ h₁).of_iso (λ_ _).symm

variable [IsNoetherianRing Λ]

/-- **Nakayama for derived complete sheaves on `X_proét`** (Stacks 09BY, in the form used for
Stacks 09C3). A sheaf of `Λ`-modules `G` whose sheaf of `\underline{Λ}`-modules is derived complete
along `I·\underline{Λ}` and with `\underline{Λ/I} ⊗ G = 0` vanishes. -/
theorem isZero_of_isDerivedComplete_of_isZero_tensor
    {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (hG : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj G)))
    (h : IsZero (quotientConstantSheaf X Λ I ⊗ G)) : IsZero G := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have h₁ := idealPowerProduct_eq_top_of_isZero_extendScalars G
    (isZero_extendScalars_of_isZero_tensor I h)
  have h₂ := isZero_of_isDerivedComplete_of_constantCoefficientIdealSheaf.{u, max (u + 1) w, w}
    X Λ I (IsNoetherian.noetherian I) _ hG h₁
  exact (E.inverse.map_isZero h₂).of_iso (E.unitIso.app G)

end Nakayama

section BaseCase

variable (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Maps out of a constant sheaf into a sheaf killed by `I` are tested on generators modulo
`I`.** -/
theorem constantSheaf_hom_ext {U : Scheme.{u}} {N N' : ModuleCat.{max (u + 1) w} Λ}
    (v : N' ⟶ N) (hv : LinearMap.range v.hom ⊔ (I • ⊤ : Submodule Λ N) = ⊤)
    {G : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)}
    (hG : ∀ a ∈ I, a • 𝟙 G = 0)
    {h₁ h₂ : (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj N ⟶ G}
    (h : (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).map v ≫ h₁ =
      (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).map v ≫ h₂) :
    h₁ = h₂ := by
  let adj := constantSheafAdj (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
    (isTerminalProEtId U)
  let Γ := (sheafSections (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj
    (op (Scheme.ProEt.mk (𝟙 U)))
  apply (adj.homEquiv N G).injective
  have hv' : v ≫ adj.homEquiv N G h₁ = v ≫ adj.homEquiv N G h₂ := by
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left, h]
  have hΓ : ∀ a ∈ I, ∀ y : Γ.obj G, a • y = 0 := fun a ha y => by
    have := congrArg (fun φ => (Γ.map φ).hom y) (hG a ha)
    rwa [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at this
  ext x
  have hx : x ∈ LinearMap.ker ((adj.homEquiv N G h₁).hom - (adj.homEquiv N G h₂).hom) := by
    have hle : LinearMap.range v.hom ⊔ (I • ⊤ : Submodule Λ N) ≤
        LinearMap.ker ((adj.homEquiv N G h₁).hom - (adj.homEquiv N G h₂).hom) := by
      refine sup_le ?_ (Submodule.smul_le.2 fun a ha n _ => ?_)
      · rintro _ ⟨y, rfl⟩
        have := congrArg (fun φ => φ.hom y) hv'
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
        simp [LinearMap.sub_apply, this]
      · simp [LinearMap.sub_apply, hΓ a ha]
    exact hle (by rw [hv]; exact Submodule.mem_top)
  simpa [sub_eq_zero] using hx

/-- Two quotients by `I` compared by a map compatible with the quotient maps: the map is an
isomorphism. -/
theorem isIso_of_isQuotientBy {U : Scheme.{u}}
    {G H H' : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)} {q : G ⟶ H}
    {q' : G ⟶ H'} (hq : Stacks.ModuleSheaf.IsQuotientBy _ Λ I G H q)
    (hq' : Stacks.ModuleSheaf.IsQuotientBy _ Λ I G H' q') {θ : H ⟶ H'} (hθ : q ≫ θ = q') :
    IsIso θ := by
  have : θ = (Stacks.ModuleSheaf.isQuotientByIso hq hq').hom :=
    (hq.2 H' hq'.1 q').unique hθ (Stacks.ModuleSheaf.isQuotientByIso_hom_comp hq hq')
  rw [this]
  infer_instance

/-- The constant sheaf of a surjection with kernel `I N` is the quotient by `I`. -/
theorem isQuotientBy_constantSheaf_map {U : Scheme.{u}} {N M : ModuleCat.{max (u + 1) w} Λ}
    (g : N ⟶ M) (hg : Function.Surjective g.hom) (hker : LinearMap.ker g.hom = I • ⊤) :
    Stacks.ModuleSheaf.IsQuotientBy (Scheme.ProEt.topology U) Λ I
      ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj N)
      ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj M)
      ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).map g) := by
  let c := constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
  let gbar : ModuleCat.of Λ (N ⧸ (I • ⊤ : Submodule Λ N)) ≅ M :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (g.hom.quotKerEquivOfSurjective hg)).toModuleIso
  have h := Stacks.ModuleSheaf.isQuotientBy_of_iso_target (c.mapIso gbar)
    (Stacks.ModuleSheaf.isQuotientBy_constantSheaf (Scheme.ProEt.topology U) Λ I N)
  have hcomp : c.map (ModuleCat.ofHom (I • (⊤ : Submodule Λ N)).mkQ) ≫ (c.mapIso gbar).hom =
      c.map g := by
    rw [Functor.mapIso_hom, ← c.map_comp]
    congr 1
  rwa [hcomp] at h

/-- The reduction map `F → F ⊗ \underline{Λ/I}` followed by the braiding is `reductionMap`. -/
theorem rightReduction_comp_braiding {U : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)) :
    ((ρ_ F).inv ≫ F ◁ constantQuotientMap I) ≫ (β_ F (quotientConstantSheaf U Λ I)).hom =
      reductionMap I F := by
  rw [Category.assoc, BraidedCategory.braiding_naturality_right, ← Category.assoc,
    rightUnitor_inv_braiding]
  rfl

end BaseCase

/-- For a `Λ^∧`-module `M`, the submodule `IΛ^∧·M` and the `Λ`-submodule `I·M` of `M` read over
`Λ` have the same elements. -/
theorem mem_completedCoefficientIdeal_smul_top_iff (Λ : Type v) [CommRing Λ] (I : Ideal Λ)
    (M : ModuleCat.{v} (AdicCompletion I Λ)) (y : M) :
    y ∈ (completedCoefficientIdeal Λ I • (⊤ : Submodule (AdicCompletion I Λ) M)) ↔
      (show (restrictToCoefficients.{v, v} Λ I).obj M from y) ∈
        (I • ⊤ : Submodule Λ ((restrictToCoefficients.{v, v} Λ I).obj M)) := by
  let : Module Λ M := Module.compHom M (algebraMap Λ (AdicCompletion I Λ))
  have : IsScalarTower Λ (AdicCompletion I Λ) M :=
    ⟨fun a b y => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have h := Ideal.smul_restrictScalars I (⊤ : Submodule (AdicCompletion I Λ) M)
  rw [Submodule.restrictScalars_top] at h
  rw [← Submodule.restrictScalars_mem Λ, h]
  rfl

section Construction

section Coefficients

variable (Λ : Type v) [CommRing Λ] (I : Ideal Λ)
  (Mbar : ModuleCat.{v} Λ) [Module (Λ ⧸ I) Mbar] [IsScalarTower Λ (Λ ⧸ I) Mbar]

/-- The `Λ`-linear map `Λ^∧ → M`, `a ↦ ā • m`, for a `Λ/I`-module `M`, where `ā ∈ Λ/I` is the
image of `a` under `Λ^∧ → Λ/I`. -/
def evalOneSMulHom (m : Mbar) :
    (restrictToCoefficients.{v, v} Λ I).obj
      (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)) ⟶ Mbar :=
  ModuleCat.ofHom
    { toFun := fun a => AdicCompletion.evalOneₐ I (show AdicCompletion I Λ from a) • m
      map_add' := fun a b => by
        change AdicCompletion.evalOneₐ I (a + b) • m = _
        rw [map_add, add_smul]
      map_smul' := fun l a => by
        change AdicCompletion.evalOneₐ I (algebraMap Λ (AdicCompletion I Λ) l *
          (show AdicCompletion I Λ from a)) • m = l • (AdicCompletion.evalOneₐ I
            (show AdicCompletion I Λ from a) • m)
        rw [map_mul, mul_smul, AlgHom.commutes, algebraMap_smul] }

/-- The value of `evalOneSMulHom`. -/
theorem evalOneSMulHom_apply (m : Mbar) (a : AdicCompletion I Λ) :
    (evalOneSMulHom Λ I Mbar m).hom a = AdicCompletion.evalOneₐ I a • m :=
  rfl

/-- `Λ → Λ^∧ → M` is `l ↦ l • m`. -/
theorem adicCompletionUnitHom_comp_evalOneSMulHom (m : Mbar) :
    adicCompletionUnitHom I ≫ evalOneSMulHom Λ I Mbar m =
      ModuleCat.ofHom (LinearMap.toSpanSingleton Λ Mbar m) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun l => ?_)
  show AdicCompletion.evalOneₐ I (algebraMap Λ (AdicCompletion I Λ) l) • m = l • m
  rw [AlgHom.commutes, algebraMap_smul]

/-- `Λ → Λ^∧` is surjective modulo `I`. -/
theorem range_adicCompletionUnitHom_sup_smul_top [IsNoetherianRing Λ] :
    LinearMap.range (adicCompletionUnitHom I).hom ⊔
      (I • ⊤ : Submodule Λ ((restrictToCoefficients.{v, v} Λ I).obj
        (ModuleCat.of (AdicCompletion I Λ) (AdicCompletion I Λ)))) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨l, hl⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalOneₐ I (show AdicCompletion I Λ from a))
  have hmem : (show AdicCompletion I Λ from a) - algebraMap Λ (AdicCompletion I Λ) l ∈
      I.map (algebraMap Λ (AdicCompletion I Λ)) := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I (IsNoetherian.noetherian I), RingHom.mem_ker]
    show AdicCompletion.evalOneₐ I _ = 0
    rw [map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, hl, sub_self]
  rw [show a = (adicCompletionUnitHom I).hom l + (a - (adicCompletionUnitHom I).hom l) by abel]
  refine Submodule.add_mem_sup ⟨l, rfl⟩ ?_
  rwa [mem_smul_top_restrictToCoefficients_iff, Ideal.smul_top_eq_map]

end Coefficients

variable (Λ : Type (max (u + 1) w)) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
  (Mbar : ModuleCat.{max (u + 1) w} Λ) [Module (Λ ⧸ I) Mbar] [IsScalarTower Λ (Λ ⧸ I) Mbar]

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- **The comparison map out of a completed constant sheaf.** Let `F` be a sheaf of `Λ`-modules
with derived complete sections over the w-contractible affines, `χ : F → \underline{M}` a map to
the constant sheaf of a `Λ/I`-module, and `s_j` global sections of `F` lifting the constant
sections `m_j`. For every `Λ^∧`-linear `β : P → (Λ^∧)^r` there is `ψ : \underline{P}^∧ → F` whose
composite with `\underline{P} → \underline{P}^∧` and `χ` is the constant sheaf of
`x ↦ ∑ (β x)_j • m_j`. -/
theorem exists_completedConstantSheafUnit_comp_eq {U : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ))
    (hF : ∀ W : U.ProEt, Scheme.ProEt.IsAffineWContractible W →
      IsDerivedCompleteModule I (F.obj.obj (op W)))
    (hMbar : ∀ x ∈ I, ∀ m : Mbar, x • m = 0)
    (χ : F ⟶ (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj Mbar)
    {r : ℕ} (m : Fin r → Mbar) (s : Fin r → F.obj.obj (op (Scheme.ProEt.mk (𝟙 U))))
    (hs : ∀ j, (χ.hom.app (op (Scheme.ProEt.mk (𝟙 U)))).hom (s j) =
      ((constantSheafAdj (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
        (isTerminalProEtId U)).unit.app Mbar).hom (m j))
    (P : ModuleCat.{max (u + 1) w} (AdicCompletion I Λ))
    (β : P →ₗ[AdicCompletion I Λ] (Fin r → AdicCompletion I Λ)) :
    ∃ ψ : (completedConstantSheafFunctor U I).obj
        ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj P) ⟶ F,
      completedConstantSheafUnit U I _ ≫ ψ ≫ χ =
        (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).map
          (∑ j, (restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).map
            (ModuleCat.ofHom (LinearMap.proj j ∘ₗ β)) ≫ evalOneSMulHom Λ I Mbar (m j)) := by
  let c := constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
  let ρ := restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I
  let Ĉ := completedConstantSheafFunctor U I (Λ := Λ)
  let adj := constantSheafAdj (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
    (isTerminalProEtId U)
  let uA := adicCompletionUnitHom I (Λ := Λ)
  have := isIso_completedConstantSheafFunctor_map_adicCompletionUnitHom.{u, w} (X := U) (I := I)
  choose t ht using fun j => (existsUnique_completedConstantSheafMap_comp U I F hF
    ((adj.homEquiv _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (s j))))).exists
  have hj : ∀ j, completedConstantSheafUnit U I (ρ.obj (ModuleCat.of (AdicCompletion I Λ)
      (AdicCompletion I Λ))) ≫ inv (Ĉ.map uA) ≫ t j ≫ χ =
      c.map (evalOneSMulHom Λ I Mbar (m j)) := fun j => by
    refine constantSheaf_hom_ext Λ I uA (range_adicCompletionUnitHom_sup_smul_top Λ I)
      (fun a ha => smul_id_constantSheaf_eq_zero (Y := U) I hMbar ha) ?_
    have h₁ := completedConstantSheafUnit_naturality U I uA
    have h₂ : ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (s j)) ≫
        ((sheafSections (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj
          (op (Scheme.ProEt.mk (𝟙 U)))).map χ =
        ModuleCat.ofHom (LinearMap.toSpanSingleton Λ Mbar (m j)) ≫ adj.unit.app Mbar := by
      refine ModuleCat.hom_ext (LinearMap.ext fun l => ?_)
      show (χ.hom.app (op (Scheme.ProEt.mk (𝟙 U)))).hom (l • s j) =
        (adj.unit.app Mbar).hom (l • m j)
      rw [map_smul, map_smul, hs j]
    rw [← Category.assoc, h₁, Category.assoc, IsIso.hom_inv_id_assoc,
      completedConstantSheafUnit_unitModule]
    calc completedConstantSheafMap U I ≫ t j ≫ χ = (completedConstantSheafMap U I ≫ t j) ≫ χ :=
          (Category.assoc _ _ _).symm
      _ = (adj.homEquiv _ F).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (s j))) ≫ χ := by
          rw [ht j]
      _ = c.map uA ≫ c.map (evalOneSMulHom Λ I Mbar (m j)) := by
          rw [← Adjunction.homEquiv_naturality_right_symm, h₂,
            Adjunction.homEquiv_naturality_left_symm, ← c.map_comp,
            adicCompletionUnitHom_comp_evalOneSMulHom]
          refine (congrArg _ ((adj.homEquiv _ _).symm_apply_eq.2 ?_)).trans (Category.comp_id _)
          rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
          exact (Category.comp_id _).symm
  refine ⟨∑ j, Ĉ.map (ρ.map (ModuleCat.ofHom (LinearMap.proj j ∘ₗ β))) ≫ inv (Ĉ.map uA) ≫ t j,
    ?_⟩
  rw [Preadditive.sum_comp, Preadditive.comp_sum, Functor.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Functor.map_comp, ← hj]
  simp only [Category.assoc]
  exact (completedConstantSheafUnit_naturality_assoc U I _ _).symm

end Construction

section Assembly

variable (Λ : Type (max (u + 1) w)) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)

attribute [local instance] SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- **A map of derived complete sheaves which is an isomorphism modulo `I` is an isomorphism**,
provided `Tor₁` of the target against `\underline{Λ/I}` vanishes. The cokernel and the kernel are
derived complete (Stacks 099Q) and vanish modulo `I`, hence vanish (Stacks 09BY). -/
theorem isIso_of_isIso_whiskerLeft_quotientConstantSheaf {U : Scheme.{u}}
    {A F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)} (Ψ : A ⟶ F)
    (hA : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} U Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} U Λ).functor.obj A)))
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} U Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} U Λ).functor.obj F)))
    (htor : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf U Λ I) ⊗
        (DerivedCategory.singleFunctor _ 0).obj F)))
    (hΨ : IsIso (quotientConstantSheaf U Λ I ◁ Ψ)) : IsIso Ψ := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} U Λ
  let Q := quotientConstantSheaf U Λ I
  have hP := derivedCompleteSheaves_isWeakSerreClass.{u, max (u + 1) w, w} U Λ
    (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
  have hcok : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} U Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj (E.functor.obj (cokernel Ψ))) :=
    (RingedSite.isDerivedComplete_iff_of_iso _ _ ((DerivedCategory.singleFunctor _ 0).mapIso
      (PreservesCokernel.iso E.functor Ψ))).2
      (@ObjectProperty.prop_cokernel _ _ _ _ hP.toIsClosedUnderCokernels _ _ (E.functor.map Ψ) _
        hA hF)
  have hQcok : IsZero (Q ⊗ cokernel Ψ) := by
    refine IsZero.of_iso ?_ (PreservesCokernel.iso (tensorLeft Q) Ψ)
    have : Epi ((tensorLeft Q).map Ψ) := @IsIso.epi_of_iso _ _ _ _ _ hΨ
    have h0 : cokernel.π ((tensorLeft Q).map Ψ) = 0 := by
      rw [← cancel_epi ((tensorLeft Q).map Ψ), cokernel.condition, comp_zero]
    have : Epi (0 : Q ⊗ F ⟶ cokernel ((tensorLeft Q).map Ψ)) := h0 ▸ inferInstance
    exact IsZero.of_epi_zero (Q ⊗ F) _
  have hepi : Epi Ψ :=
    Preadditive.epi_of_isZero_cokernel Ψ (isZero_of_isDerivedComplete_of_isZero_tensor I hcok hQcok)
  have hker : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} U Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj (E.functor.obj (kernel Ψ))) :=
    (RingedSite.isDerivedComplete_iff_of_iso _ _ ((DerivedCategory.singleFunctor _ 0).mapIso
      (PreservesKernel.iso E.functor Ψ))).2
      (@ObjectProperty.prop_kernel _ _ _ _ hP.toIsClosedUnderKernels _ _ (E.functor.map Ψ) _
        hA hF)
  let S := ShortComplex.mk (kernel.ι Ψ) Ψ (kernel.condition Ψ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel Ψ) }
  have hm : Mono (Q ◁ kernel.ι Ψ) := mono_whiskerLeft_of_isZero_homology Q hS htor
  have hz : Q ◁ kernel.ι Ψ = 0 := by
    rw [← cancel_mono (Q ◁ Ψ), ← MonoidalCategory.whiskerLeft_comp, kernel.condition,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]
  have hQker : IsZero (Q ⊗ kernel Ψ) := by
    rw [hz] at hm
    exact IsZero.of_mono_zero _ (Q ⊗ A)
  have hmono : Mono Ψ :=
    Preadditive.mono_of_isZero_kernel Ψ (isZero_of_isDerivedComplete_of_isZero_tensor I hker hQker)
  exact isIso_of_mono_of_epi Ψ

/-- **The base case of Stacks 09C3: a sheaf with constant reduction is a completed constant
sheaf.** Let `U` be a scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `F` a sheaf of
`Λ`-modules on `U_proét` such that
* `F` is derived complete (as a sheaf of `\underline{Λ}`-modules, along `I·\underline{Λ}`);
* `H⁻¹(F ⊗_Λ^L \underline{N}) = 0` for every `Λ`-module `N` killed by `I`;
* `F ⊗ \underline{Λ/I} ≅ \underline{M̄}` for a finite `Λ`-module `M̄` killed by `I`;
* the reduction `F → F ⊗ \underline{Λ/I}` is surjective on global sections.
Then `F ≅ \underline{M}^∧` for a finite projective `Λ^∧`-module `M`.

Over a nonempty `U`, `M̄` is flat over `Λ/I` (the `Tor₁` vanishing), hence finite projective,
and lifts to a finite projective `Λ^∧`-module `M` (`exists_isCompletedCoefficientLift`). Global
sections of `F` lifting generators of `M̄` give, through a splitting of `(Λ^∧)^r → M`, a map
`\underline{M}^∧ → F` which is an isomorphism modulo `I`, hence an isomorphism
(`isIso_of_isIso_whiskerLeft_quotientConstantSheaf`). Over the empty scheme every sheaf vanishes.
This is the case `a = b` of the proof of Stacks 09C3. -/
theorem exists_iso_completedConstantSheaf_of_reduction_iso {U : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ))
    (hc : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} U Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} U Λ).functor.obj F)))
    (htor : ∀ N : ModuleCat.{max (u + 1) w} Λ, (∀ x ∈ I, ∀ n : N, x • n = 0) →
      IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗ (DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj N))))
    (Mbar : ModuleCat.{max (u + 1) w} Λ) (hMbar : ∀ x ∈ I, ∀ m : Mbar, x • m = 0)
    [Module.Finite Λ Mbar]
    (e : F ⊗ quotientConstantSheaf U Λ I ≅
      (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj Mbar)
    (hsurj : Function.Surjective (((ρ_ F).inv ≫ F ◁ (constantSheaf (Scheme.ProEt.topology U)
        (ModuleCat.{max (u + 1) w} Λ)).map (ModuleCat.ofHom
          ((Ideal.Quotient.mkₐ Λ I).toLinearMap))).hom.app (op (Scheme.ProEt.mk (𝟙 U))))) :
    ∃ M : ModuleCat.{max (u + 1) w} (AdicCompletion I Λ),
      Module.Finite (AdicCompletion I Λ) M ∧ Module.Projective (AdicCompletion I Λ) M ∧
      Nonempty (F ≅ completedConstantSheaf U Λ I
        ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).obj M)) := by
  rcases isEmpty_or_nonempty U with hU | hU
  · exact ⟨ModuleCat.of (AdicCompletion I Λ) (Fin 0 → AdicCompletion I Λ), inferInstance,
      inferInstance, ⟨(Scheme.ProEt.isZero_sheaf_of_isEmpty F).iso
        (Scheme.ProEt.isZero_sheaf_of_isEmpty _)⟩⟩
  have hI : I.FG := IsNoetherian.noetherian I
  let ρ := restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I
  let c := constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
  let Q := quotientConstantSheaf U Λ I
  let T := Scheme.ProEt.mk (𝟙 U)
  have hT : Module.IsTorsionBySet Λ Mbar I := fun x a => hMbar a a.2 x
  let : Module (Λ ⧸ I) Mbar := hT.module
  have : IsScalarTower Λ (Λ ⧸ I) Mbar := hT.isScalarTower
  have hflat : Module.Flat (Λ ⧸ I) Mbar :=
    Module.Flat.quotient_of_lTensor_injective I Mbar fun J =>
      injective_lTensor_of_isZero_homology.{u, w} I F htor Mbar e
        (N' := ModuleCat.of Λ J) (N := ModuleCat.of Λ (Λ ⧸ I))
        (ModuleCat.ofHom (J.subtype.restrictScalars Λ)) Subtype.val_injective
        (smul_eq_zero_quotient I)
  have : Module.Finite (Λ ⧸ I) Mbar := Module.Finite.of_restrictScalars_finite Λ (Λ ⧸ I) Mbar
  have : Module.FinitePresentation (Λ ⧸ I) Mbar := Module.finitePresentation_of_finite _ _
  have : Module.Projective (Λ ⧸ I) Mbar := Module.Flat.projective_of_finitePresentation
  obtain ⟨M, hMfin, hMproj, ψ₀, hψ₀⟩ :=
    exists_isCompletedCoefficientLift.{max (u + 1) w, max (u + 1) w} Λ I hI
      (ModuleCat.of (Λ ⧸ I) Mbar)
  have := hMfin
  have := hMproj
  obtain ⟨r, x, hx⟩ := Module.Finite.exists_fin (R := AdicCompletion I Λ) (M := M)
  let γ : (Fin r → AdicCompletion I Λ) →ₗ[AdicCompletion I Λ] M :=
    Fintype.linearCombination (AdicCompletion I Λ) x
  have hγ : Function.Surjective γ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hx]
  obtain ⟨β, hβ⟩ := Module.projective_lifting_property γ LinearMap.id hγ
  let mk := (completedCoefficientIdeal Λ I • (⊤ : Submodule (AdicCompletion I Λ) M)).mkQ
  let m : Fin r → Mbar := fun j => ψ₀ (mk (x j))
  let adj := constantSheafAdj (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
    (isTerminalProEtId U)
  let χ : F ⟶ c.obj Mbar := ((ρ_ F).inv ≫ F ◁ constantQuotientMap I) ≫ e.hom
  have hs : ∀ j, ∃ s, (χ.hom.app (op T)).hom s = (adj.unit.app Mbar).hom (m j) := fun j => by
    obtain ⟨s, hs⟩ := hsurj ((e.inv.hom.app (op T)).hom ((adj.unit.app Mbar).hom (m j)))
    refine ⟨s, ?_⟩
    show (e.hom.hom.app (op T)).hom
      ((((ρ_ F).inv ≫ F ◁ constantQuotientMap I).hom.app (op T)).hom s) = _
    rw [show (((ρ_ F).inv ≫ F ◁ constantQuotientMap I).hom.app (op T)).hom s = _ from hs]
    exact congrArg (fun φ => (φ.hom.app (op T)).hom ((adj.unit.app Mbar).hom (m j))) e.inv_hom_id
  choose s hs using hs
  have hF := isDerivedCompleteModule_obj_of_isDerivedComplete.{u, w} U I F _ hc (Iso.refl _)
  obtain ⟨ψ, hψ⟩ :=
    exists_completedConstantSheafUnit_comp_eq.{u, w} Λ I Mbar F hF hMbar χ m s hs M β
  let g : ρ.obj M ⟶ Mbar := ∑ j, ρ.map (ModuleCat.ofHom (LinearMap.proj j ∘ₗ β)) ≫
    evalOneSMulHom Λ I Mbar (m j)
  have hg : ∀ y : M, g.hom y = ψ₀ (mk y) := fun y => by
    have hy : y = ∑ j, β y j • x j := by
      rw [← Fintype.linearCombination_apply]
      exact (LinearMap.congr_fun hβ y).symm
    have hsum : mk y = ∑ j, Ideal.Quotient.mk (completedCoefficientIdeal Λ I) (β y j) •
        mk (x j) := by
      rw [show mk y = mk (∑ j, β y j • x j) from congrArg mk hy, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      rfl
    show (∑ j, (ρ.map (ModuleCat.ofHom (LinearMap.proj j ∘ₗ β)) ≫
      evalOneSMulHom Λ I Mbar (m j))).hom y = _
    rw [ModuleCat.hom_sum]
    refine (LinearMap.sum_apply _ _ _).trans ?_
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψ₀]
    rfl
  have hgsurj : Function.Surjective g.hom := fun z => by
    obtain ⟨y, hy⟩ := ψ₀.surjective z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨y, (hg y).trans hy⟩
  have hgker : LinearMap.ker g.hom = I • ⊤ := by
    ext y
    rw [LinearMap.mem_ker, hg y, AddEquiv.map_eq_zero_iff]
    exact (Submodule.Quotient.mk_eq_zero _).trans
      (mem_completedCoefficientIdeal_smul_top_iff Λ I M y)
  let e' : Q ⊗ F ≅ c.obj Mbar := (β_ F Q).symm ≪≫ e
  have hχ : reductionMap I F ≫ e'.hom = χ := by
    rw [← rightReduction_comp_braiding Λ I F]
    simp only [e', χ, Q, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have hθ : IsIso (Q ◁ (completedConstantSheafUnit U I (ρ.obj M) ≫ ψ) ≫ e'.hom) :=
    isIso_of_isQuotientBy.{u, w} Λ I (isQuotientBy_reductionMap.{u, w} I _)
      (isQuotientBy_constantSheaf_map.{u, w} Λ I g hgsurj hgker)
      (by rw [reductionMap_naturality_assoc, hχ, Category.assoc, hψ])
  have hΨ : IsIso (Q ◁ ψ) := by
    have h₁ := @IsIso.of_isIso_comp_right _ _ _ _ _
      (Q ◁ (completedConstantSheafUnit U I (ρ.obj M) ≫ ψ)) e'.hom _ hθ
    rw [MonoidalCategory.whiskerLeft_comp] at h₁
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (Q ◁ completedConstantSheafUnit U I (ρ.obj M))
      (Q ◁ ψ) (isIso_whiskerLeft_completedConstantSheafUnit_of_projective.{u, w} (I := I) M) h₁
  have hA : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} U Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} U Λ).functor.obj
          ((completedConstantSheafFunctor U I).obj (ρ.obj M)))) :=
    (RingedSite.isDerivedComplete_iff_of_iso _ _ ((DerivedCategory.singleFunctor _ 0).mapIso
      ((constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w} U Λ).app _))).2
      (isDerivedComplete_completedConstantCoefficientSheaf.{u, w} U I hI (ρ.obj M))
  have htor' : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
      ((DerivedCategory.singleFunctor _ 0).obj Q ⊗ (DerivedCategory.singleFunctor _ 0).obj F)) :=
    (htor _ (smul_eq_zero_quotient I)).of_iso
      ((DerivedCategory.homologyFunctor _ (-1)).mapIso (β_ _ _))
  have := isIso_of_isIso_whiskerLeft_quotientConstantSheaf.{u, w} Λ I ψ hA hc htor' hΨ
  exact ⟨M, hMfin, hMproj, ⟨(asIso ψ).symm⟩⟩

end Assembly

end AlgebraicGeometry.ProEtale
