module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.BaseChangeHomFree
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.FiniteFreeResolution
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Flat base change of the Hom complex out of a complex with finite cohomology

Let `A` be a Noetherian ring, `ρ : A ⟶ R` a flat ring map, `P` a complex of `A`-modules whose
cohomology modules are finite, and `I` a bounded complex such that both `I` and `R ⊗_A I` are
K-injective. Then the base-change map

`θ : R ⊗_A Hom^•_A(P, I) ⟶ Hom^•_A(P, R ⊗_A I)`

is a quasi-isomorphism.

The proof is degreewise. In degree `n` only the terms of `P` in degrees `≤ b - n + 1` matter,
`b` being an upper bound of `I`, so `P` may be replaced by its canonical truncation
`τ_{≤ M} P` for `M = b - n + 2`. That truncation is bounded above with finite cohomology, hence
receives a quasi-isomorphism from a complex `Q` of finite free modules; both sides of `θ` turn it
into a quasi-isomorphism (here the K-injectivity and the flatness are used), and for `Q` the map
`θ` is bijective in every degree.

## Main results

* `Stacks.FlatBaseChangeHom.theta_naturality`: `θ` is natural in `P`.
* `Stacks.FlatBaseChangeHom.quasiIso_theta`: `θ` is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex TensorProduct

universe u

namespace Stacks.FlatBaseChangeHom

variable {A R : Type u} [CommRing A] [CommRing R] (ρ : A →+* R)

/-! ### Functoriality in the source -/

section Precomp

variable {P' P : CochainComplex (ModuleCat.{u} A) ℤ} (g : P' ⟶ P)
  (I : CochainComplex (ModuleCat.{u} A) ℤ)

/-- Precomposition with `g : P' ⟶ P` on `R ⊗_A Hom^•_A(P, I)`. -/
abbrev S₀map : S₀ ρ P I ⟶ S₀ ρ P' I :=
  ((ModuleCat.extendScalars ρ ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (Stacks.HomComplex.TensorHomMap.precomp A P' P I g)

/-- Precomposition with `g : P' ⟶ P` on `Hom^•_A(P, R ⊗_A I)`. -/
abbrev T₀map : T₀ ρ P I ⟶ T₀ ρ P' I := homComplexMap g (𝟙 (REc ρ I))

omit [CommRing R] in
/-- The map `Hom^•(P, Y) ⟶ Hom^•(P', Y)` induced by `g : P' ⟶ P` sends a cochain `z` to the
composite `g ∘ z`. -/
lemma homComplexMap_id_f_apply {Y : CochainComplex (ModuleCat.{u} A) ℤ} (n : ℤ)
    (z : Cochain P Y n) :
    (homComplexMap g (𝟙 Y)).f n z = (Cochain.ofHom g).comp z (zero_add n) := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [homComplexMap_f_apply, cochainMap_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.comp_id]

/-- `T₀map ρ g I` sends a cochain `z` of `Hom^•_A(P, R ⊗_A I)` to the composite `g ∘ z`. -/
lemma T₀map_f_apply (n : ℤ) (z : Cochain P (REc ρ I) n) :
    (T₀map ρ g I).f n z = (Cochain.ofHom g).comp z (zero_add n) :=
  homComplexMap_id_f_apply g n z

/-- **`θ` is natural in the source complex.** -/
lemma theta_naturality :
    theta ρ P I ≫ T₀map ρ g I = S₀map ρ g I ≫ theta ρ P' I := by
  ext n : 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  change (T₀map ρ g I).f n (thetaLin ρ P I n x) = thetaLin ρ P' I n
    (LinearMap.lTensor (RR ρ) ((Stacks.HomComplex.TensorHomMap.precomp A P' P I g).f n).hom x)
  rw [T₀map_f_apply]
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    change (Cochain.ofHom g).comp (thetaCochain ρ P I b c) (zero_add n) =
      thetaCochain ρ P' I b ((Cochain.ofHom g).comp c (zero_add n))
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, thetaCochain_v ρ P' I b _ p q hpq,
      thetaCochain_v ρ P I b c p q hpq, ← Category.assoc]
    erw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  | add x y hx hy => rw [map_add, Cochain.comp_add, hx, hy, map_add, map_add]

/-- If precomposition with `g` is a quasi-isomorphism in degree `n` on both sides of `θ`, and `θ`
is one for `P'`, then `θ` is a quasi-isomorphism in degree `n` for `P`. -/
private lemma quasiIsoAt_theta_of_quasiIsoAt_precomp (n : ℤ)
    (_ : QuasiIsoAt (S₀map ρ g I) n) (_ : QuasiIsoAt (T₀map ρ g I) n)
    (_ : QuasiIsoAt (theta ρ P' I) n) :
    QuasiIsoAt (theta ρ P I) n := by
  have : QuasiIsoAt (theta ρ P I ≫ T₀map ρ g I) n := by
    rw [theta_naturality]
    infer_instance
  exact quasiIsoAt_of_comp_right _ (T₀map ρ g I) n

end Precomp

/-! ### Precomposition with a map which is an isomorphism on a window -/

section Window

/-- **Precomposition with a map `g` is bijective on degree-`k` cochains into `Y` as soon as, in
every degree `p`, either `g` is an isomorphism or `Y` vanishes in degree `p + k`.** -/
lemma bijective_precomp_of_window {K' K Y : CochainComplex (ModuleCat.{u} A) ℤ} (g : K' ⟶ K)
    (k : ℤ) (hg : ∀ p, IsIso (g.f p) ∨ IsZero (Y.X (p + k))) :
    Function.Bijective (fun z : Cochain K Y k => (Cochain.ofHom g).comp z (zero_add k)) := by
  classical
  refine ⟨fun z z' h => ?_, fun w => ?_⟩
  · refine Cochain.ext _ _ (fun p q hpq => ?_)
    subst hpq
    have h' := Cochain.congr_v h p (p + k) rfl
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h'
    rcases hg p with hp | hp
    · exact (cancel_epi (g.f p)).1 h'
    · exact hp.eq_of_tgt _ _
  · refine ⟨Cochain.mk (fun p q hpq =>
      if hp : IsIso (g.f p) then inv (g.f p) ≫ w.v p q hpq else 0), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
    split_ifs with hp
    · rw [IsIso.hom_inv_id_assoc]
    · subst hpq
      exact ((hg p).resolve_left hp).eq_of_tgt _ _

/-- A morphism of cochain complexes which is an isomorphism in degrees `n - 1`, `n`, `n + 1` is a
quasi-isomorphism in degree `n`. -/
lemma quasiIsoAt_of_isIso_f {C : Type*} [Category C] [HasZeroMorphisms C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) [K.HasHomology n] [L.HasHomology n]
    (h₁ : IsIso (φ.f (n - 1))) (h₂ : IsIso (φ.f n)) (h₃ : IsIso (φ.f (n + 1))) :
    QuasiIsoAt φ n := by
  rw [quasiIsoAt_iff]
  have : IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ) := by
    have : IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ).τ₁ := by
      change IsIso (φ.f ((ComplexShape.up ℤ).prev n))
      rw [CochainComplex.prev]
      exact h₁
    have : IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ).τ₃ := by
      change IsIso (φ.f ((ComplexShape.up ℤ).next n))
      rw [CochainComplex.next]
      exact h₃
    have : IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ).τ₂ := h₂
    exact ShortComplex.isIso_of_isIso _
  infer_instance

end Window

/-! ### Quasi-isomorphisms -/

section QuasiIso

variable {P' P : CochainComplex (ModuleCat.{u} A) ℤ} (g : P' ⟶ P)
  (I : CochainComplex (ModuleCat.{u} A) ℤ)

/-- The forgetful identification of the `A`-module Hom complex with the Hom complex of abelian
groups. -/
def homComplexRForgetIso (K L : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.HomComplexR A K L) ≅ K.HomComplex L :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- **Precomposition with a quasi-isomorphism is a quasi-isomorphism of `A`-module Hom complexes
into a K-injective complex.** -/
lemma quasiIso_precomp [QuasiIso g] [I.IsKInjective] :
    QuasiIso (Stacks.HomComplex.TensorHomMap.precomp A P' P I g) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]
  refine (quasiIso_iff_of_arrow_mk_iso _ (homComplexMap g (𝟙 I))
    (Arrow.isoMk (homComplexRForgetIso P I) (homComplexRForgetIso P' I) ?_)).2
    (homComplexMap_quasiIso g (𝟙 I))
  ext n : 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_)
  change Cochain P I n at z
  exact homComplexMap_id_f_apply g n z

/-- **Precomposition with a quasi-isomorphism is a quasi-isomorphism on `R ⊗_A Hom^•_A(-, I)`**
for `I` K-injective and `R` flat over `A`. -/
lemma quasiIso_S₀map (hρ : ρ.Flat) [QuasiIso g] [I.IsKInjective] :
    QuasiIso (S₀map ρ g I) := by
  have : (ModuleCat.extendScalars ρ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hρ
  have : PreservesFiniteColimits (ModuleCat.extendScalars ρ) := by
    have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars ρ) :=
      (ModuleCat.extendRestrictScalarsAdj ρ).leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesFiniteLimits (ModuleCat.extendScalars ρ ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (ModuleCat.extendScalars ρ ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) := comp_preservesFiniteColimits _ _
  have := quasiIso_precomp g I
  exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _

/-- **Precomposition with a quasi-isomorphism is a quasi-isomorphism on `Hom^•_A(-, R ⊗_A I)`**
for `R ⊗_A I` K-injective. -/
lemma quasiIso_T₀map [QuasiIso g] [(REc ρ I).IsKInjective] : QuasiIso (T₀map ρ g I) :=
  homComplexMap_quasiIso g (𝟙 _)

end QuasiIso

/-! ### Auxiliary results for the main theorem -/

/-- The canonical truncation `τ_{≤ M} P` of a complex with finite cohomology modules has finite
cohomology modules. -/
private lemma finite_homology_truncLE (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ℤ) (hP : ∀ i, Module.Finite A (P.homology i)) (i : ℤ) :
    Module.Finite A ((P.truncLE M).homology i) := by
  by_cases hi : i ≤ M
  · have := CochainComplex.quasiIsoAt_ιTruncLE P M i hi
    exact Module.Finite.equiv
      (asIso (HomologicalComplex.homologyMap (P.ιTruncLE M) i)).symm.toLinearEquiv
  · have : Subsingleton ((P.truncLE M).homology i) :=
      ModuleCat.isZero_iff_subsingleton.1 ((P.truncLE M).isZero_of_isLE M i (by omega))
    infer_instance

/-- `θ` is a quasi-isomorphism for a complex `Q` of finite free modules and a bounded `I`. -/
private lemma quasiIso_theta_of_finiteFree (Q I : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [I.IsStrictlyGE a] [I.IsStrictlyLE b]
    (hQ : ∀ p, Module.Finite A (Q.X p) ∧ Module.Free A (Q.X p)) :
    QuasiIso (theta ρ Q I) := by
  have : ∀ k, IsIso ((theta ρ Q I).f k) := fun k =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_theta_f ρ Q I a b hQ k)
  have := HomologicalComplex.Hom.isIso_of_components (theta ρ Q I)
  infer_instance

/-- If `I` is strictly `≤ b`, so is `R ⊗_A I`. -/
private lemma isStrictlyLE_REc (I : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [I.IsStrictlyLE b] :
    (REc ρ I).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (RE ρ).map_isZero (I.isZero_of_isStrictlyLE b i hi)

/-- In every degree `p`, either the inclusion `τ_{≤ M} P ⟶ P` is an isomorphism, or a complex `Y`
strictly `≤ b` vanishes in degree `p + k`, provided `b < M + k`. -/
private lemma isIso_ιTruncLE_f_or_isZero (P Y : CochainComplex (ModuleCat.{u} A) ℤ) (M b k : ℤ)
    [Y.IsStrictlyLE b] (hk : b < M + k) (p : ℤ) :
    IsIso ((P.ιTruncLE M).f p) ∨ IsZero (Y.X (p + k)) := by
  by_cases hp : p < M
  · exact Or.inl (P.isIso_ιTruncLE_f_of_lt M p hp)
  · exact Or.inr (Y.isZero_of_isStrictlyLE b _ (by omega))

/-! ### The main result -/

/-- **Flat base change of the Hom complex.** Let `A` be Noetherian and `ρ : A ⟶ R` flat. For a
complex `P` of `A`-modules with finite cohomology modules and a bounded complex `I` such that `I`
and `R ⊗_A I` are K-injective, the base-change map
`θ : R ⊗_A Hom^•_A(P, I) ⟶ Hom^•_A(P, R ⊗_A I)` is a quasi-isomorphism. -/
theorem quasiIso_theta [IsNoetherianRing A] (hρ : ρ.Flat) (P I : CochainComplex (ModuleCat.{u} A) ℤ)
    (a b : ℤ) [I.IsStrictlyGE a] [I.IsStrictlyLE b] [I.IsKInjective] [(REc ρ I).IsKInjective]
    (hP : ∀ i, Module.Finite A (P.homology i)) :
    QuasiIso (theta ρ P I) := by
  rw [quasiIso_iff]
  intro n
  let τ := P.truncLE (b - n + 2)
  let ι := P.ιTruncLE (b - n + 2)
  obtain ⟨Q, h, hQ, _, hh⟩ :=
    exists_quasiIso_finiteFree_of_isStrictlyLE τ (b - n + 2) (finite_homology_truncLE P _ hP)
  have := quasiIso_theta_of_finiteFree ρ Q I a b hQ
  have := isStrictlyLE_REc ρ I b
  have hS : ∀ k, n - 1 ≤ k → IsIso ((S₀map ρ ι I).f k) := by
    intro k hk
    have : IsIso ((Stacks.HomComplex.TensorHomMap.precomp A τ P I ι).f k) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (bijective_precomp_of_window ι k
          (isIso_ιTruncLE_f_or_isZero P I (b - n + 2) b k (by omega)))
    exact Functor.map_isIso
      (ModuleCat.extendScalars ρ ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      ((Stacks.HomComplex.TensorHomMap.precomp A τ P I ι).f k)
  have hT : ∀ k, n - 1 ≤ k → IsIso ((T₀map ρ ι I).f k) := by
    intro k hk
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    have hf : ((T₀map ρ ι I).f k : _ → _) =
        fun z : Cochain P (REc ρ I) k => (Cochain.ofHom ι).comp z (zero_add k) :=
      funext (T₀map_f_apply ρ ι I k)
    rw [hf]
    exact bijective_precomp_of_window ι k
      (isIso_ιTruncLE_f_or_isZero P _ (b - n + 2) b k (by omega))
  have key : ∀ {K L : CochainComplex AddCommGrpCat.{u} ℤ} (φ : K ⟶ L),
      (∀ k, n - 1 ≤ k → IsIso (φ.f k)) → QuasiIsoAt φ n := fun φ hφ =>
    quasiIsoAt_of_isIso_f φ n (hφ _ (by omega)) (hφ _ (by omega)) (hφ _ (by omega))
  have hSn := key _ hS
  have hTn := key _ hT
  have := quasiIso_S₀map ρ h I hρ
  have := quasiIso_T₀map ρ h I
  exact quasiIsoAt_theta_of_quasiIsoAt_precomp ρ ι I n hSn hTn
    (quasiIsoAt_theta_of_quasiIsoAt_precomp ρ h I n inferInstance inferInstance inferInstance)

end Stacks.FlatBaseChangeHom

end
