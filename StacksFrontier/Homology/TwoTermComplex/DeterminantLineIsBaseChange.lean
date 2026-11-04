module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine
public import StacksFrontier.Algebra.Module.Projective.Determinant.AlongBaseChange
public import StacksFrontier.Algebra.Module.Projective.Determinant.RetractBaseChange

/-!
# Base change of the determinant line of a two-term complex

Let `R → S` be a homomorphism of commutative rings and `K : K₁ → K₀` a two-term complex of finite
projective `R`-modules. A base change `σ` of `K` to a two-term complex `K' : K'₁ → K'₀` of finite
projective `S`-modules, degreewise `K'ᵢ = S ⊗_R Kᵢ`, induces a map of determinant lines
`det(K) → det(K')` exhibiting `det(K')` as `S ⊗_R det(K)`. It carries the canonical element
`δ(K)` of a rank-zero complex to `δ(K')`, it is compatible with composition along a tower of
rings, and it intertwines the determinant equivalences of a degreewise-surjective
quasi-isomorphism and of its base change.

## Main definitions

* `TwoTermComplex.detLineMap`: the base change map `det(K) → det(K')`.

## Main results

* `TwoTermComplex.isBaseChange_detLineMap`: it is a base change.
* `TwoTermComplex.detLineMap_delta`: it carries `δ(K)` to `δ(K')`.
* `TwoTermComplex.detLineMap_comp`: compatibility with a tower `R → S → T`.
* `TwoTermComplex.kernelDeterminantEquiv_isBaseChange`: the determinant isomorphism of the short
  exact sequence of a surjection commutes with base change.
* `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_isBaseChange`: the determinant equivalence
  of a degreewise-surjective quasi-isomorphism commutes with base change.
-/

@[expose] public noncomputable section

universe u

open TensorProduct ProjectiveDeterminant

namespace TwoTermComplex

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

section DetLine

variable {K₁ K₀ : Type u} [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁]
  [Module.Projective R K₁] [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀]
  [Module.Projective R K₀]
variable {K'₁ K'₀ : Type u} [AddCommGroup K'₁] [Module R K'₁] [Module S K'₁]
  [IsScalarTower R S K'₁] [Module.Finite S K'₁] [Module.Projective S K'₁]
  [AddCommGroup K'₀] [Module R K'₀] [Module S K'₀] [IsScalarTower R S K'₀]
  [Module.Finite S K'₀] [Module.Projective S K'₀]
variable {σ₁ : K₁ →ₗ[R] K'₁} (h₁ : IsBaseChange S σ₁) {σ₀ : K₀ →ₗ[R] K'₀}
  (h₀ : IsBaseChange S σ₀)

/-- **The base change of determinant lines.** For degreewise base changes `σᵢ : Kᵢ → K'ᵢ`, the
map `det(K) → det(K')` sending `φ : det K₁ → det K₀` to the unique `S`-linear map
`det K'₁ → det K'₀` whose composite with `det σ₁` is `det σ₀ ∘ φ`. -/
def detLineMap (K : K₁ →ₗ[R] K₀) (K' : K'₁ →ₗ[S] K'₀) :
    determinantLine K →ₗ[R] determinantLine K' :=
  IsBaseChange.linearMapLeftRightHom (isBaseChange_detMap h₁)
    (detMap σ₀ (span_range_eq_top_of_isBaseChange h₀))

/-- The base change `detLineMap h₁ h₀ K K' φ` agrees with `det σ₀ ∘ φ` on the image of
`det σ₁`. -/
theorem detLineMap_apply (K : K₁ →ₗ[R] K₀) (K' : K'₁ →ₗ[S] K'₀) (φ : determinantLine K)
    (x : ProjectiveDeterminant.module (R := R) (M := K₁)) :
    detLineMap h₁ h₀ K K' φ (detMap σ₁ (span_range_eq_top_of_isBaseChange h₁) x) =
      detMap σ₀ (span_range_eq_top_of_isBaseChange h₀) (φ x) :=
  IsBaseChange.linearMapLeftRightHom_comp_apply _ _ _ _

omit [Module R K'₀] [IsScalarTower R S K'₀] in
/-- Two elements of the base-changed determinant line agree as soon as they agree on the
images of the determinant line of `K₁`. -/
theorem detLine_ext {K' : K'₁ →ₗ[S] K'₀} {Ψ Ψ' : determinantLine K'}
    (h : ∀ x : ProjectiveDeterminant.module (R := R) (M := K₁),
      Ψ (detMap σ₁ (span_range_eq_top_of_isBaseChange h₁) x) =
        Ψ' (detMap σ₁ (span_range_eq_top_of_isBaseChange h₁) x)) : Ψ = Ψ' :=
  (isBaseChange_detMap h₁).algHom_ext _ _ h

/-- **The base change of determinant lines is a base change.** -/
theorem isBaseChange_detLineMap (K : K₁ →ₗ[R] K₀) (K' : K'₁ →ₗ[S] K'₀) :
    IsBaseChange S (detLineMap h₁ h₀ K K') := by
  let := ProjectiveDeterminant.invertible (R := R) (M := K₁)
  exact IsBaseChange.linearMapLeftRight_of_projective _ (isBaseChange_detMap h₀)

include h₁ h₀ in
/-- Rank zero is preserved by base change. -/
theorem isRankZero_of_isBaseChange {K : K₁ →ₗ[R] K₀} (K' : K'₁ →ₗ[S] K'₀) (hK : IsRankZero K) :
    IsRankZero K' := fun q => by
  rw [rankAtStalk_of_isBaseChange h₁, rankAtStalk_of_isBaseChange h₀, hK]

/-- **The base change of determinant lines preserves the canonical element.** -/
theorem detLineMap_delta {K : K₁ →ₗ[R] K₀} {K' : K'₁ →ₗ[S] K'₀}
    (hc : (K'.restrictScalars R).comp σ₁ = σ₀.comp K) (hK : IsRankZero K) :
    detLineMap h₁ h₀ K K' (delta K hK) = delta K' (isRankZero_of_isBaseChange h₁ h₀ K' hK) := by
  refine detLine_ext h₁ fun x => ?_
  rw [detLineMap_apply]
  apply Subtype.ext
  show exteriorMap (S := S) σ₀ (ExteriorAlgebra.map K x.1) =
    ExteriorAlgebra.map K' (exteriorMap (S := S) σ₁ x.1)
  rw [exteriorMap_map, map_exteriorMap, hc]

end DetLine

section Comp

variable {T : Type u} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable {K₁ K₀ : Type u} [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁]
  [Module.Projective R K₁] [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀]
  [Module.Projective R K₀]
variable {K'₁ K'₀ : Type u} [AddCommGroup K'₁] [Module R K'₁] [Module S K'₁]
  [IsScalarTower R S K'₁] [Module.Finite S K'₁] [Module.Projective S K'₁]
  [AddCommGroup K'₀] [Module R K'₀] [Module S K'₀] [IsScalarTower R S K'₀]
  [Module.Finite S K'₀] [Module.Projective S K'₀]
variable {K''₁ K''₀ : Type u} [AddCommGroup K''₁] [Module R K''₁] [Module S K''₁] [Module T K''₁]
  [IsScalarTower R S K''₁] [IsScalarTower S T K''₁] [IsScalarTower R T K''₁]
  [Module.Finite T K''₁] [Module.Projective T K''₁]
  [AddCommGroup K''₀] [Module R K''₀] [Module S K''₀] [Module T K''₀]
  [IsScalarTower R S K''₀] [IsScalarTower S T K''₀] [IsScalarTower R T K''₀]
  [Module.Finite T K''₀] [Module.Projective T K''₀]
variable {σ₁ : K₁ →ₗ[R] K'₁} (h₁ : IsBaseChange S σ₁) {σ₀ : K₀ →ₗ[R] K'₀}
  (h₀ : IsBaseChange S σ₀)
variable {τ₁ : K'₁ →ₗ[S] K''₁} (k₁ : IsBaseChange T τ₁) {τ₀ : K'₀ →ₗ[S] K''₀}
  (k₀ : IsBaseChange T τ₀)

/-- **The base change of determinant lines is compatible with a tower of rings.** -/
theorem detLineMap_comp (K : K₁ →ₗ[R] K₀) (K' : K'₁ →ₗ[S] K'₀) (K'' : K''₁ →ₗ[T] K''₀)
    (φ : determinantLine K) :
    detLineMap (h₁.comp k₁) (h₀.comp k₀) K K'' φ =
      detLineMap k₁ k₀ K' K'' (detLineMap h₁ h₀ K K' φ) := by
  refine detLine_ext (h₁.comp k₁) fun x => ?_
  rw [detLineMap_apply]
  have e1 := detMap_comp σ₁ (span_range_eq_top_of_isBaseChange h₁) τ₁
    (span_range_eq_top_of_isBaseChange k₁)
    (span_range_eq_top_of_isBaseChange (h₁.comp k₁)) x
  have e0 := detMap_comp σ₀ (span_range_eq_top_of_isBaseChange h₀) τ₀
    (span_range_eq_top_of_isBaseChange k₀)
    (span_range_eq_top_of_isBaseChange (h₀.comp k₀)) (φ x)
  rw [e1, e0, detLineMap_apply, detLineMap_apply]

end Comp

section Kernel

variable {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
variable {M' N' : Type u} [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  [Module.Finite S M'] [Module.Projective S M']
  [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
  [Module.Finite S N'] [Module.Projective S N']

private theorem coe_kernelDeterminantEquiv {P Q : Type u} [AddCommGroup P] [Module S P]
    [Module.Finite S P] [Module.Projective S P] [AddCommGroup Q] [Module S Q]
    [Module.Finite S Q] [Module.Projective S Q]
    (f : P →ₗ[S] Q) (hf : Function.Surjective f)
    [Module.Finite S (LinearMap.ker f)] [Module.Projective S (LinearMap.ker f)]
    (x : ProjectiveDeterminant.module (R := S) (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := S) (M := Q)) (z : ExteriorAlgebra S P)
    (hz : ExteriorAlgebra.map f z = (y : ExteriorAlgebra S Q)) :
    ((kernelDeterminantEquiv f hf (x ⊗ₜ[S] y) :
      ProjectiveDeterminant.module (R := S) (M := P)) : ExteriorAlgebra S P) =
      ExteriorAlgebra.map (LinearMap.ker f).subtype (x : ExteriorAlgebra S (LinearMap.ker f)) *
        z := by
  have hγ := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
    f.exact_subtype_ker_map hf).property (determinantAnnihilatorEquiv x)
      (determinantAnnihilatorEquiv y) z (by simpa [determinantAnnihilatorEquiv] using hz)
  simpa [kernelDeterminantEquiv, determinantAnnihilatorEquiv] using hγ

/-- **The determinant isomorphism of the short exact sequence of a surjection commutes with base
change.** -/
theorem kernelDeterminantEquiv_isBaseChange (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (f' : M' →ₗ[S] N') (hf' : Function.Surjective f')
    {σ : M →ₗ[R] M'} (hσ : IsBaseChange S σ) {ν : N →ₗ[R] N'} (hν : IsBaseChange S ν)
    (hc : (f'.restrictScalars R).comp σ = ν.comp f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    [Module.Finite S (LinearMap.ker f')] [Module.Projective S (LinearMap.ker f')]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := R) (M := N)) :
    kernelDeterminantEquiv f' hf'
        (detMap (IsBaseChange.kerRestrict f f' σ ν hc)
          (span_range_eq_top_of_isBaseChange (IsBaseChange.ker_restrict f' hσ hν hc hf)) x ⊗ₜ[S]
          detMap ν (span_range_eq_top_of_isBaseChange hν) y) =
      detMap σ (span_range_eq_top_of_isBaseChange hσ)
        (kernelDeterminantEquiv f hf (x ⊗ₜ[R] y)) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hlift : ExteriorAlgebra.map f (ExteriorAlgebra.map s (y : ExteriorAlgebra R N)) =
      (y : ExteriorAlgebra R N) := by
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hs, ExteriorAlgebra.map_id,
      AlgHom.id_apply]
  apply Subtype.ext
  rw [coe_detMap, coe_kernelDeterminantEquiv f hf x y _ hlift,
    coe_kernelDeterminantEquiv f' hf' _ _ (exteriorMap (S := S) σ
      (ExteriorAlgebra.map s (y : ExteriorAlgebra R N))) ?_]
  · rw [map_mul, coe_detMap, map_exteriorMap, exteriorMap_map]
    have : ((LinearMap.ker f').subtype.restrictScalars R).comp
        (IsBaseChange.kerRestrict f f' σ ν hc) = σ.comp (LinearMap.ker f).subtype :=
      LinearMap.ext fun _ => rfl
    rw [this, exteriorMap_map]
  · rw [coe_detMap, map_exteriorMap, hc, ← exteriorMap_map ν f, hlift]

end Kernel


section QuasiIso

variable {K₁ K₀ L₁ L₀ : Type u}
  [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
  [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
  [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
  [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
variable {K'₁ K'₀ L'₁ L'₀ : Type u}
  [AddCommGroup K'₁] [Module R K'₁] [Module S K'₁] [IsScalarTower R S K'₁]
  [Module.Finite S K'₁] [Module.Projective S K'₁]
  [AddCommGroup K'₀] [Module R K'₀] [Module S K'₀] [IsScalarTower R S K'₀]
  [Module.Finite S K'₀] [Module.Projective S K'₀]
  [AddCommGroup L'₁] [Module R L'₁] [Module S L'₁] [IsScalarTower R S L'₁]
  [Module.Finite S L'₁] [Module.Projective S L'₁]
  [AddCommGroup L'₀] [Module R L'₀] [Module S L'₀] [IsScalarTower R S L'₀]
  [Module.Finite S L'₀] [Module.Projective S L'₀]

/-- The canonical element of an acyclic rank-zero complex generates its target: the map of
determinant lines induced by a bijection is bijective. -/
private theorem surjective_delta_of_bijective {P Q : Type u} [AddCommGroup P] [Module S P]
    [Module.Finite S P] [Module.Projective S P] [AddCommGroup Q] [Module S Q]
    [Module.Finite S Q] [Module.Projective S Q] (d : P →ₗ[S] Q) (hr : IsRankZero d)
    (hd : Function.Bijective d) : Function.Surjective (delta d hr) :=
  (ProjectiveDeterminant.map_bijective (LinearEquiv.ofBijective d hd)).2

/-- **The determinant equivalence of a degreewise-surjective quasi-isomorphism commutes with base
change.** Let `a : K → L` be a degreewise-surjective quasi-isomorphism of two-term complexes of
finite projective `R`-modules and `a' : K' → L'` one of two-term complexes of finite projective
`S`-modules, and let `K'`, `L'` be degreewise base changes of `K`, `L` compatibly with `a` and
`a'`. Then the base change of determinant lines intertwines the determinant equivalences of `a`
and of `a'`. -/
theorem determinantEquivOfSurjectiveQuasiIso_isBaseChange
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (K' : K'₁ →ₗ[S] K'₀) (L' : L'₁ →ₗ[S] L'₀)
    {σ₁ : K₁ →ₗ[R] K'₁} (hσ₁ : IsBaseChange S σ₁) {σ₀ : K₀ →ₗ[R] K'₀} (hσ₀ : IsBaseChange S σ₀)
    {τ₁ : L₁ →ₗ[R] L'₁} (hτ₁ : IsBaseChange S τ₁) {τ₀ : L₀ →ₗ[R] L'₀} (hτ₀ : IsBaseChange S τ₀)
    (hK : (K'.restrictScalars R).comp σ₁ = σ₀.comp K)
    (a : Hom K L) (a' : Hom K' L')
    (hneg : (a'.neg.restrictScalars R).comp σ₁ = τ₁.comp a.neg)
    (hzero : (a'.zero.restrictScalars R).comp σ₀ = τ₀.comp a.zero)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (ha' : a'.IsDegreewiseSurjective) (hqa' : a'.IsQuasiIso) (φ : determinantLine K) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    letI : Module.Finite S (LinearMap.ker a'.neg) := kernel_finite a'.neg ha'.1
    letI : Module.Projective S (LinearMap.ker a'.neg) := kernel_projective a'.neg ha'.1
    letI : Module.Finite S (LinearMap.ker a'.zero) := kernel_finite a'.zero ha'.2
    letI : Module.Projective S (LinearMap.ker a'.zero) := kernel_projective a'.zero ha'.2
    (determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').equiv (detLineMap hσ₁ hσ₀ K K' φ) =
      detLineMap hτ₁ hτ₀ L L' ((determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv φ) := by
  have ha1 : Function.Surjective a.neg := ha.1
  have ha2 : Function.Surjective a.zero := ha.2
  have ha'1 : Function.Surjective a'.neg := ha'.1
  have ha'2 : Function.Surjective a'.zero := ha'.2
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha2
  let : Module.Finite S (LinearMap.ker a'.neg) := kernel_finite a'.neg ha'1
  let : Module.Projective S (LinearMap.ker a'.neg) := kernel_projective a'.neg ha'1
  let : Module.Finite S (LinearMap.ker a'.zero) := kernel_finite a'.zero ha'2
  let : Module.Projective S (LinearMap.ker a'.zero) := kernel_projective a'.zero ha'2
  have hκ₁ := IsBaseChange.ker_restrict a'.neg hσ₁ hτ₁ hneg ha1
  have hκ₀ := IsBaseChange.ker_restrict a'.zero hσ₀ hτ₀ hzero ha2
  have hkd : (a'.kernelDifferential.restrictScalars R).comp
      (IsBaseChange.kerRestrict a.neg a'.neg σ₁ τ₁ hneg) =
      (IsBaseChange.kerRestrict a.zero a'.zero σ₀ τ₀ hzero).comp a.kernelDifferential := by
    ext x
    have := LinearMap.congr_fun hK x.1
    simpa [Hom.kernelDifferential] using this
  have hδ (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :
      delta a'.kernelDifferential
          (determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').kernelRankZero
          (detMap (IsBaseChange.kerRestrict a.neg a'.neg σ₁ τ₁ hneg)
            (span_range_eq_top_of_isBaseChange hκ₁) x) =
        detMap (IsBaseChange.kerRestrict a.zero a'.zero σ₀ τ₀ hzero)
          (span_range_eq_top_of_isBaseChange hκ₀)
          (delta a.kernelDifferential
            (determinantEquivOfSurjectiveQuasiIso K L a ha hqa).kernelRankZero x) := by
    rw [← detLineMap_apply hκ₁ hκ₀, detLineMap_delta hκ₁ hκ₀ hkd]
  have key (y : ProjectiveDeterminant.module (R := R) (M := L₁))
      (x' : ProjectiveDeterminant.module (R := S) (M := LinearMap.ker a'.neg)) :
      kernelDeterminantEquiv a'.zero ha'2 (delta a'.kernelDifferential
          (determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').kernelRankZero x' ⊗ₜ[S]
          (determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').equiv
            (detLineMap hσ₁ hσ₀ K K' φ) (detMap τ₁ (span_range_eq_top_of_isBaseChange hτ₁) y)) =
        kernelDeterminantEquiv a'.zero ha'2 (delta a'.kernelDifferential
          (determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').kernelRankZero x' ⊗ₜ[S]
          detLineMap hτ₁ hτ₀ L L' ((determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv φ)
            (detMap τ₁ (span_range_eq_top_of_isBaseChange hτ₁) y)) := by
    have hx' : x' ∈ Submodule.span S (Set.range
        (detMap (IsBaseChange.kerRestrict a.neg a'.neg σ₁ τ₁ hneg)
          (span_range_eq_top_of_isBaseChange hκ₁))) := by
      rw [span_range_eq_top_of_isBaseChange (isBaseChange_detMap hκ₁)]
      trivial
    induction hx' using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        rw [(determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').compatibility,
          kernelDeterminantEquiv_isBaseChange a.neg ha1 a'.neg ha'1 hσ₁ hτ₁ hneg,
          detLineMap_apply, ← (determinantEquivOfSurjectiveQuasiIso K L a ha hqa).compatibility,
          ← kernelDeterminantEquiv_isBaseChange a.zero ha2 a'.zero ha'2 hσ₀ hτ₀ hzero, hδ,
          detLineMap_apply]
    | zero => simp
    | add z w _ _ hz hw => rw [map_add, add_tmul, add_tmul, map_add, map_add, hz, hw]
    | smul c z _ hz => rw [map_smul, ← smul_tmul', ← smul_tmul', map_smul, map_smul, hz]
  refine detLine_ext hτ₁ fun y => ?_
  let := ProjectiveDeterminant.invertible (R := S) (M := LinearMap.ker a'.zero)
  refine sub_eq_zero.mp (Module.Invertible.eq_zero_of_forall_tmul_eq_zero
    (R := S) (Z := ProjectiveDeterminant.module (R := S) (M := LinearMap.ker a'.zero)) fun z => ?_)
  obtain ⟨x', rfl⟩ := surjective_delta_of_bijective _
    (determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').kernelRankZero
    (determinantEquivOfSurjectiveQuasiIso K' L' a' ha' hqa').kernelAcyclic z
  rw [tmul_sub, sub_eq_zero]
  exact (kernelDeterminantEquiv a'.zero ha'2).injective (key y x')

end QuasiIso

end TwoTermComplex

end
