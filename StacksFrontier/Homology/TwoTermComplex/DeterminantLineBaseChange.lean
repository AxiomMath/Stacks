module

public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChange
public import StacksFrontier.Homology.TwoTermComplex.DeterminantEquivIso
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChangeVanishing

/-!
# Base change of the determinant line of a two-term complex

Let `R → A` be a map of commutative rings and let `K : K₁ → K₀` be a two-term complex of finite
projective `R`-modules. Its base change `K.baseChange A : A ⊗_R K₁ → A ⊗_R K₀` is a two-term
complex of finite projective `A`-modules, and the determinant line commutes with base change: the
determinant line of `K.baseChange A` is the base change of the determinant line of `K`, the
canonical element `δ` of a rank-zero complex goes to the canonical element, and the isomorphism
of determinant lines induced by a degreewise-surjective quasi-isomorphism goes to the one
induced by its base change. The base change is transitive along a tower `R → A → A'` and is the
identity along `R → R`.

The file also contains the elementary calculus of morphisms of two-term complexes: identities,
composites, the criterion for a degreewise-surjective morphism to be a quasi-isomorphism in terms
of its kernel complex, and the equivalence of determinant lines `TwoTermComplex.Hom.detEquiv`,
with its behaviour under composition, identities and morphisms that are bijective in both
degrees.

## Main definitions

* `TwoTermComplex.kernelBaseChangeEquiv`: the kernel of the base change of a surjection onto a
  projective module is the base change of its kernel.
* `TwoTermComplex.Hom.id`: the identity morphism of a two-term complex.
* `TwoTermComplex.Hom.detEquiv`: the equivalence of determinant lines induced by a
  degreewise-surjective quasi-isomorphism.
* `TwoTermComplex.determinantLineBaseChangeMap`: the base change of an element of the
  determinant line.
* `TwoTermComplex.determinantLineBaseChange`: the determinant line commutes with base change,
  `A ⊗_R det(K) ≃ det(A ⊗_R K)`.
* `TwoTermComplex.Hom.cancelBaseChange`, `TwoTermComplex.Hom.lid`: the comparisons
  `A' ⊗_A (A ⊗_R K) ≅ A' ⊗_R K` and `R ⊗_R K ≅ K`.

## Main results

* `TwoTermComplex.Hom.isQuasiIso_iff_bijective_kernelDifferential`: a degreewise-surjective
  morphism is a quasi-isomorphism exactly when its kernel complex is acyclic.
* `TwoTermComplex.Hom.IsQuasiIso.baseChange`: base change preserves degreewise-surjective
  quasi-isomorphisms.
* `TwoTermComplex.Hom.detEquiv_comp`, `TwoTermComplex.Hom.detEquiv_id`,
  `TwoTermComplex.Hom.detEquiv_delta`, `TwoTermComplex.Hom.detEquiv_eq_arrowCongr_of_bijective`:
  composition, identities, the canonical element, and morphisms bijective in both degrees.
* `TwoTermComplex.determinantLineBaseChangeMap_delta`: base change carries `δ` to `δ`.
* `TwoTermComplex.Hom.detEquiv_baseChange` (also stated as
  `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_baseChange`): **the equivalence of
  determinant lines of a degreewise-surjective quasi-isomorphism commutes with base change.**
* `TwoTermComplex.Hom.detEquiv_cancelBaseChange`, `TwoTermComplex.Hom.detEquiv_lid`:
  transitivity along a tower, and base change along the identity.

## Implementation notes

The base change of an element of the determinant line is the base change of the underlying map
of determinants, read through `ProjectiveDeterminant.baseChangeEquiv`.

## References

* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
* [Stacks Project, Tag 0FJL](https://stacks.math.columbia.edu/tag/0FJL)
* [Stacks Project, Tag 0FLA](https://stacks.math.columbia.edu/tag/0FLA)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ProjectiveDeterminant

section

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The base-change comparison of exterior algebras is natural in the module. -/
theorem exteriorAlgebraBaseChange_map (f : M →ₗ[R] N) (z : ExteriorAlgebra A (A ⊗[R] M)) :
    exteriorAlgebraBaseChange R A N (ExteriorAlgebra.map (f.baseChange A) z) =
      Algebra.TensorProduct.map (AlgHom.id A A) (ExteriorAlgebra.map f)
        (exteriorAlgebraBaseChange R A M z) := by
  have h : (exteriorAlgebraBaseChange R A N).toAlgHom.comp
        (ExteriorAlgebra.map (f.baseChange A)) =
      (Algebra.TensorProduct.map (AlgHom.id A A) (ExteriorAlgebra.map f)).comp
        (exteriorAlgebraBaseChange R A M).toAlgHom := by
    ext m
    simp [exteriorAlgebraBaseChange_ι]
  exact DFunLike.congr_fun h z

/-- The inverse base-change comparison of exterior algebras is natural in the module, on pure
tensors. -/
theorem map_baseChange_exteriorAlgebraBaseChange_symm_tmul (f : M →ₗ[R] N) (a : A)
    (z : ExteriorAlgebra R M) :
    ExteriorAlgebra.map (f.baseChange A) ((exteriorAlgebraBaseChange R A M).symm (a ⊗ₜ[R] z)) =
      (exteriorAlgebraBaseChange R A N).symm (a ⊗ₜ[R] ExteriorAlgebra.map f z) := by
  apply (exteriorAlgebraBaseChange R A N).injective
  rw [exteriorAlgebraBaseChange_map, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rfl

end

section

universe u v w

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]

/-- The determinant map of a base change is the base change of the determinant map. -/
theorem map_baseChange_baseChangeEquiv_tmul
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (h' : ∀ p : PrimeSpectrum A,
      Module.rankAtStalk (A ⊗[R] M) p = Module.rankAtStalk (A ⊗[R] N) p)
    (f : M →ₗ[R] N) (a : A) (x : module (R := R) (M := M)) :
    map h' (f.baseChange A) (baseChangeEquiv (a ⊗ₜ[R] x)) =
      baseChangeEquiv (a ⊗ₜ[R] map h f x) :=
  Subtype.ext (map_baseChange_exteriorAlgebraBaseChange_symm_tmul A f a x.1)

end

/-- The inverse of the determinant map of a linear equivalence is the determinant map of its
inverse. -/
theorem mapEquiv_symm_apply {R : Type*} [CommRing R] {N₁ N₂ : Type*}
    [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [Module.Projective R N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] [Module.Projective R N₂]
    (e : N₁ ≃ₗ[R] N₂) (y : ProjectiveDeterminant.module (R := R) (M := N₂)) :
    (mapEquiv e).symm y = mapEquiv e.symm y := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  show y.1 = ExteriorAlgebra.map e.toLinearMap (ExteriorAlgebra.map e.symm.toLinearMap y.1)
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, LinearEquiv.comp_coe,
    LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id,
    AlgHom.id_apply]

section Tower

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (A' : Type*) [CommRing A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The inverse base-change comparison of exterior algebras on degree-one generators. -/
theorem exteriorAlgebraBaseChange_symm_one_tmul_ι (m : M) :
    (exteriorAlgebraBaseChange R A M).symm (1 ⊗ₜ[R] ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι A (1 ⊗ₜ[R] m) := by
  rw [AlgEquiv.symm_apply_eq, exteriorAlgebraBaseChange_ι]

/-- The base-change comparisons of exterior algebras along a tower `R → A → A'` compose to the
comparison along `R → A'`, read through `A' ⊗_A (A ⊗_R M) ≃ A' ⊗_R M`. -/
theorem map_cancelBaseChange_exteriorAlgebraBaseChange_symm (a : A) (a' : A')
    (z : ExteriorAlgebra R M) :
    ExteriorAlgebra.map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' M).toLinearMap
        ((exteriorAlgebraBaseChange A A' (A ⊗[R] M)).symm
          (a' ⊗ₜ[A] (exteriorAlgebraBaseChange R A M).symm (a ⊗ₜ[R] z))) =
      (exteriorAlgebraBaseChange R A' M).symm ((a • a') ⊗ₜ[R] z) := by
  let F₁ : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A' (A' ⊗[R] M) :=
    (AlgHom.restrictScalars R (ExteriorAlgebra.map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' M).toLinearMap)).comp <|
      (((exteriorAlgebraBaseChange A A' (A ⊗[R] M)).symm.toAlgHom.restrictScalars R).comp <|
        (((Algebra.TensorProduct.includeRight :
          ExteriorAlgebra A (A ⊗[R] M) →ₐ[A] A' ⊗[A] ExteriorAlgebra A (A ⊗[R] M)).restrictScalars
            R).comp <|
          (((exteriorAlgebraBaseChange R A M).symm.toAlgHom.restrictScalars R).comp
            Algebra.TensorProduct.includeRight)))
  let F₂ : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A' (A' ⊗[R] M) :=
    ((exteriorAlgebraBaseChange R A' M).symm.toAlgHom.restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  have hF : F₁ = F₂ := by
    ext m
    simp [F₁, F₂, exteriorAlgebraBaseChange_symm_one_tmul_ι]
  have h₁ : a' ⊗ₜ[A] (exteriorAlgebraBaseChange R A M).symm (a ⊗ₜ[R] z) =
      (a • a') • ((1 : A') ⊗ₜ[A] (exteriorAlgebraBaseChange R A M).symm (1 ⊗ₜ[R] z)) := by
    rw [TensorProduct.tmul_eq_smul_one_tmul a z, map_smul, ← TensorProduct.smul_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h₁, TensorProduct.tmul_eq_smul_one_tmul (a • a') z, map_smul, map_smul, map_smul]
  exact congrArg ((a • a') • ·) (DFunLike.congr_fun hF z)

/-- The base-change comparison of exterior algebras along the identity of `R`, read through
`R ⊗_R M ≃ M`. -/
theorem map_lid_exteriorAlgebraBaseChange_symm (r : R) (z : ExteriorAlgebra R M) :
    ExteriorAlgebra.map (TensorProduct.lid R M).toLinearMap
        ((exteriorAlgebraBaseChange R R M).symm (r ⊗ₜ[R] z)) = r • z := by
  let F : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
    (ExteriorAlgebra.map (TensorProduct.lid R M).toLinearMap).comp <|
      (exteriorAlgebraBaseChange R R M).symm.toAlgHom.comp Algebra.TensorProduct.includeRight
  have hF : F = AlgHom.id R _ := by
    ext m
    simp [F, exteriorAlgebraBaseChange_symm_one_tmul_ι]
  rw [TensorProduct.tmul_eq_smul_one_tmul r z, map_smul, map_smul]
  exact congrArg (r • ·) (DFunLike.congr_fun hF z)

end Tower

section TowerDeterminant

universe u v

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (A' : Type u) [CommRing A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]

/-- The base-change comparisons of determinant lines along a tower `R → A → A'` compose to the
comparison along `R → A'`, read through `A' ⊗_A (A ⊗_R M) ≃ A' ⊗_R M`. -/
theorem mapEquiv_cancelBaseChange_baseChangeEquiv_tmul (a : A) (a' : A')
    (y : ProjectiveDeterminant.module (R := R) (M := M)) :
    mapEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' M)
        (baseChangeEquiv (a' ⊗ₜ[A] baseChangeEquiv (a ⊗ₜ[R] y))) =
      baseChangeEquiv ((a • a') ⊗ₜ[R] y) :=
  Subtype.ext (map_cancelBaseChange_exteriorAlgebraBaseChange_symm A A' M a a' y.1)

/-- The base-change comparison of determinant lines along the identity of `R`, read through
`R ⊗_R M ≃ M`. -/
theorem mapEquiv_lid_baseChangeEquiv_tmul (r : R)
    (y : ProjectiveDeterminant.module (R := R) (M := M)) :
    mapEquiv (TensorProduct.lid R M) (baseChangeEquiv (r ⊗ₜ[R] y)) = r • y :=
  Subtype.ext (map_lid_exteriorAlgebraBaseChange_symm M r y.1)

end TowerDeterminant

end ProjectiveDeterminant

namespace TwoTermComplex

open ProjectiveDeterminant

section Kernel

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The kernel of the base change of a surjection onto a projective module is the base change of
its kernel. -/
def kernelBaseChangeEquiv [Module.Projective R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : A ⊗[R] LinearMap.ker f ≃ₗ[A] LinearMap.ker (f.baseChange A) := by
  refine LinearEquiv.ofBijective
    (((LinearMap.ker f).subtype.baseChange A).codRestrict _
      fun t => by
        rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
          LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]) ?_
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let p : M →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - s.comp f) fun x => by
      rw [LinearMap.mem_ker]
      simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
        sub_eq_zero] using (LinearMap.congr_fun hs (f x)).symm
  have hp : p.comp (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    simp [p]
  have hp' : (LinearMap.ker f).subtype.comp p = LinearMap.id - s.comp f := rfl
  constructor
  · intro t t' htt'
    have h := congrArg (fun z => p.baseChange A (z : A ⊗[R] M)) (congrArg Subtype.val htt')
    simp only [LinearMap.codRestrict_apply] at h
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hp,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at h
  · intro z
    refine ⟨p.baseChange A z, Subtype.ext ?_⟩
    rw [LinearMap.codRestrict_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hp',
      LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.baseChange_comp,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, z.2, map_zero, sub_zero]

/-- `TwoTermComplex.kernelBaseChangeEquiv` is the base change of the inclusion of the kernel. -/
theorem coe_kernelBaseChangeEquiv [Module.Projective R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (t : A ⊗[R] LinearMap.ker f) :
    (kernelBaseChangeEquiv A f hf t : A ⊗[R] M) = (LinearMap.ker f).subtype.baseChange A t :=
  rfl

end Kernel

section Hom

variable {R : Type*} [CommRing R]
variable {K₁ K₀ L₁ L₀ M₁ M₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]
variable [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₀] [Module R L₀]
variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₀] [Module R M₀]

namespace Hom

/-- The identity morphism of a two-term complex. -/
def id (K : K₁ →ₗ[R] K₀) : Hom K K where
  neg := LinearMap.id
  zero := LinearMap.id
  comm := rfl

variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀} {M : M₁ →ₗ[R] M₀}

/-- The identity morphism is degreewise surjective. -/
theorem isDegreewiseSurjective_id (K : K₁ →ₗ[R] K₀) : (Hom.id K).IsDegreewiseSurjective :=
  ⟨Function.surjective_id, Function.surjective_id⟩

/-- A composite of degreewise-surjective morphisms is degreewise surjective. -/
theorem IsDegreewiseSurjective.comp {b : Hom L M} {a : Hom K L}
    (hb : b.IsDegreewiseSurjective) (ha : a.IsDegreewiseSurjective) :
    (b.comp a).IsDegreewiseSurjective :=
  ⟨hb.1.comp ha.1, hb.2.comp ha.2⟩

/-- A morphism whose two components are bijective is degreewise surjective. -/
theorem IsDegreewiseSurjective.of_bijective {a : Hom K L} (hn : Function.Bijective a.neg)
    (hz : Function.Bijective a.zero) : a.IsDegreewiseSurjective :=
  ⟨hn.2, hz.2⟩

/-- The identity morphism is a quasi-isomorphism. -/
theorem isQuasiIso_id (K : K₁ →ₗ[R] K₀) : (Hom.id K).IsQuasiIso := by
  have hn : (Hom.id K).hMinus = LinearMap.id := by ext x; rfl
  have hz : (Hom.id K).hZero = LinearMap.id := by ext x; rfl
  rw [IsQuasiIso, hn, hz]
  exact ⟨Function.bijective_id, Function.bijective_id⟩

/-- A composite of quasi-isomorphisms is a quasi-isomorphism. -/
theorem IsQuasiIso.comp {b : Hom L M} {a : Hom K L} (hb : b.IsQuasiIso) (ha : a.IsQuasiIso) :
    (b.comp a).IsQuasiIso := by
  have hn : (b.comp a).hMinus = b.hMinus.comp a.hMinus := by ext x; rfl
  have hz : (b.comp a).hZero = b.hZero.comp a.hZero := by ext x; rfl
  rw [IsQuasiIso, hn, hz]
  exact ⟨hb.1.comp ha.1, hb.2.comp ha.2⟩

/-- A degreewise-surjective morphism of two-term complexes is a quasi-isomorphism exactly when
the differential of its kernel complex is bijective. -/
theorem isQuasiIso_iff_bijective_kernelDifferential (a : Hom K L)
    (ha : a.IsDegreewiseSurjective) :
    a.IsQuasiIso ↔ Function.Bijective a.kernelDifferential := by
  constructor
  · intro hqa
    constructor
    · intro x y hxy
      have hKxy : K (x : K₁) = K (y : K₁) := congrArg Subtype.val hxy
      let z' : LinearMap.ker K := ⟨x - y, by
        rw [LinearMap.mem_ker, map_sub]
        exact sub_eq_zero.mpr hKxy⟩
      have hminus : a.hMinus z' = a.hMinus 0 := by
        apply Subtype.ext
        show a.neg (x - y) = a.neg 0
        rw [map_sub, x.property, y.property, sub_self, map_zero]
      exact Subtype.ext (sub_eq_zero.mp (congrArg Subtype.val (hqa.1.1 hminus)))
    · intro z
      have hzq : a.hZero (Submodule.Quotient.mk z.1) = a.hZero 0 := by
        rw [map_zero]
        show Submodule.Quotient.mk (a.zero z.1) = 0
        rw [z.property]
        rfl
      obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp (hqa.2.1 hzq)
      have hL : L (a.neg x) = 0 := by
        rw [← LinearMap.comp_apply, ← a.comm, LinearMap.comp_apply, hx]
        exact z.property
      obtain ⟨k, hk⟩ := hqa.1.2 ⟨a.neg x, hL⟩
      refine ⟨⟨x - k, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, map_sub]
        have hkval : a.neg (k : K₁) = a.neg x := congrArg Subtype.val hk
        rw [hkval, sub_self]
      · apply Subtype.ext
        show K (x - (k : K₁)) = z
        rw [map_sub, hx]
        exact sub_eq_self.mpr k.property
  · intro hd
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro x y hxy
      have hk : (x : K₁) - y ∈ LinearMap.ker a.neg := by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact congrArg Subtype.val hxy
      have h0 : a.kernelDifferential ⟨_, hk⟩ = a.kernelDifferential 0 := by
        apply Subtype.ext
        show K ((x : K₁) - y) = K 0
        rw [map_sub, x.property, y.property, sub_self, map_zero]
      exact Subtype.ext (sub_eq_zero.mp (congrArg Subtype.val (hd.1 h0)))
    · intro y
      obtain ⟨x, hx⟩ := ha.1 y.1
      have hKx : K x ∈ LinearMap.ker a.zero := by
        rw [LinearMap.mem_ker, ← LinearMap.comp_apply, a.comm, LinearMap.comp_apply, hx]
        exact y.property
      obtain ⟨k, hk⟩ := hd.2 ⟨K x, hKx⟩
      have hKk : K (k : K₁) = K x := congrArg Subtype.val hk
      refine ⟨⟨x - k, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, map_sub, hKk, sub_self]
      · apply Subtype.ext
        show a.neg (x - (k : K₁)) = y
        rw [map_sub, k.property, sub_zero, hx]
    · intro x y hxy
      induction x using Submodule.Quotient.induction_on with | _ x =>
      induction y using Submodule.Quotient.induction_on with | _ y =>
      change Submodule.Quotient.mk (a.zero x) = Submodule.Quotient.mk (a.zero y) at hxy
      rw [Submodule.Quotient.eq] at hxy ⊢
      obtain ⟨w, hw⟩ := hxy
      obtain ⟨v, rfl⟩ := ha.1 w
      have hk : x - y - K v ∈ LinearMap.ker a.zero := by
        rw [LinearMap.mem_ker, map_sub, map_sub, ← LinearMap.comp_apply a.zero K, a.comm,
          LinearMap.comp_apply, hw, sub_self]
      obtain ⟨k, hk'⟩ := hd.2 ⟨_, hk⟩
      refine ⟨v + k, ?_⟩
      have hKk : K (k : K₁) = x - y - K v := congrArg Subtype.val hk'
      rw [map_add, hKk]
      abel
    · intro y
      induction y using Submodule.Quotient.induction_on with | _ y =>
      obtain ⟨x, rfl⟩ := ha.2 y
      exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- A morphism whose two components are bijective is a quasi-isomorphism. -/
theorem isQuasiIso_of_bijective (a : Hom K L) (hn : Function.Bijective a.neg)
    (hz : Function.Bijective a.zero) : a.IsQuasiIso := by
  rw [isQuasiIso_iff_bijective_kernelDifferential a (.of_bijective hn hz)]
  exact ⟨fun x y _ => Subtype.ext (hn.1 (x.2.trans y.2.symm)),
    fun z => ⟨0, Subtype.ext ((map_zero K).trans (hz.1 (z.2.trans (map_zero a.zero).symm)).symm)⟩⟩

end Hom

end Hom

section HomBaseChange

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
variable {K₁ K₀ L₁ L₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]
variable [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₀] [Module R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}

namespace Hom

variable {A} in
/-- The base change of a degreewise-surjective morphism is degreewise surjective. -/
theorem IsDegreewiseSurjective.baseChange {a : Hom K L} (ha : a.IsDegreewiseSurjective) :
    (a.baseChange A).IsDegreewiseSurjective :=
  ⟨LinearMap.lTensor_surjective A ha.1, LinearMap.lTensor_surjective A ha.2⟩

variable [Module.Projective R L₁] [Module.Projective R L₀]

/-- The kernel complex of the base change of a degreewise-surjective morphism is the base change
of its kernel complex. -/
theorem kernelDifferential_baseChange (a : Hom K L) (ha : a.IsDegreewiseSurjective) :
    (a.baseChange A).kernelDifferential ∘ₗ (kernelBaseChangeEquiv A a.neg ha.1).toLinearMap =
      (kernelBaseChangeEquiv A a.zero ha.2).toLinearMap ∘ₗ a.kernelDifferential.baseChange A := by
  ext x
  rfl

/-- The base change of a degreewise-surjective quasi-isomorphism is a quasi-isomorphism. -/
theorem IsQuasiIso.baseChange {a : Hom K L} (hqa : a.IsQuasiIso)
    (ha : a.IsDegreewiseSurjective) : (a.baseChange A).IsQuasiIso := by
  rw [isQuasiIso_iff_bijective_kernelDifferential _ ha.baseChange]
  rw [isQuasiIso_iff_bijective_kernelDifferential _ ha] at hqa
  have h := kernelDifferential_baseChange A a ha
  have hbc : Function.Bijective (a.kernelDifferential.baseChange A) :=
    (LinearEquiv.baseChange R A _ _ (LinearEquiv.ofBijective _ hqa)).bijective
  have hc : (a.baseChange A).kernelDifferential =
      (kernelBaseChangeEquiv A a.zero ha.2).toLinearMap ∘ₗ a.kernelDifferential.baseChange A ∘ₗ
        (kernelBaseChangeEquiv A a.neg ha.1).symm.toLinearMap :=
    LinearMap.ext fun x => (congrArg _ (LinearEquiv.apply_symm_apply _ x).symm).trans
      (LinearMap.congr_fun h ((kernelBaseChangeEquiv A a.neg ha.1).symm x))
  rw [hc]
  exact (kernelBaseChangeEquiv A a.zero ha.2).bijective.comp
    (hbc.comp (kernelBaseChangeEquiv A a.neg ha.1).symm.bijective)

end Hom

end HomBaseChange

section Determinant

universe u v w v₁ v₀ w₁ w₀

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The determinant of the short exact sequence of a surjection, computed in the exterior
algebra: `x ⊗ y` goes to `x * z` for any lift `z` of `y`. -/
theorem coe_kernelDeterminantEquiv_tmul {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := R) (M := N)) (z : ExteriorAlgebra R M)
    (hz : ExteriorAlgebra.map f z = y) :
    (kernelDeterminantEquiv f hf (x ⊗ₜ[R] y) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map (LinearMap.ker f).subtype x * z :=
  (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
      f.exact_subtype_ker_map hf).property (determinantAnnihilatorEquiv x)
      (determinantAnnihilatorEquiv y) z hz

/-- The determinant of the short exact sequence of a surjection commutes with base change. -/
theorem kernelDeterminantEquiv_baseChange_tmul {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    (hf' : Function.Surjective (f.baseChange A))
    [Module.Finite A (LinearMap.ker (f.baseChange A))]
    [Module.Projective A (LinearMap.ker (f.baseChange A))]
    (a b : A) (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := R) (M := N)) :
    kernelDeterminantEquiv (f.baseChange A) hf'
        (mapEquiv (kernelBaseChangeEquiv A f hf) (baseChangeEquiv (a ⊗ₜ[R] x)) ⊗ₜ[A]
          baseChangeEquiv (b ⊗ₜ[R] y)) =
      baseChangeEquiv ((a * b) ⊗ₜ[R] kernelDeterminantEquiv f hf (x ⊗ₜ[R] y)) := by
  obtain ⟨z, hz⟩ := (ExteriorAlgebra.map_surjective_iff.mpr hf) (y : ExteriorAlgebra R N)
  apply Subtype.ext
  rw [coe_kernelDeterminantEquiv_tmul _ _ _ _ ((exteriorAlgebraBaseChange R A M).symm
    (b ⊗ₜ[R] z)) (by
      rw [map_baseChange_exteriorAlgebraBaseChange_symm_tmul, hz]
      rfl),
    coe_baseChangeEquiv_tmul, coe_kernelDeterminantEquiv_tmul f hf x y z hz]
  have hsub : (LinearMap.ker (f.baseChange A)).subtype ∘ₗ
      (kernelBaseChangeEquiv A f hf).toLinearMap = (LinearMap.ker f).subtype.baseChange A := rfl
  show ExteriorAlgebra.map (LinearMap.ker (f.baseChange A)).subtype
      (ExteriorAlgebra.map (kernelBaseChangeEquiv A f hf).toLinearMap
        ((exteriorAlgebraBaseChange R A (LinearMap.ker f)).symm
          (a ⊗ₜ[R] (x : ExteriorAlgebra R (LinearMap.ker f))))) * _ = _
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hsub,
    map_baseChange_exteriorAlgebraBaseChange_symm_tmul, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

end Determinant

section DetEquiv

universe u v₁ v₀ w₁ w₀ x₁ x₀

variable {R : Type u} [CommRing R]
variable {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
  {M₁ : Type x₁} {M₀ : Type x₀}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
variable [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁] [Module.Projective R M₁]
variable [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀] [Module.Projective R M₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀} {M : M₁ →ₗ[R] M₀}

namespace Hom

/-- The equivalence of determinant lines induced by a degreewise-surjective quasi-isomorphism,
`TwoTermComplex.determinantEquivOfSurjectiveQuasiIso`. -/
abbrev detEquiv (a : Hom K L) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) :
    determinantLine K ≃ₗ[R] determinantLine L :=
  letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  (determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv

/-- The equivalence of determinant lines `TwoTermComplex.Hom.detEquiv` carries the canonical
element to the canonical element (Stacks 0FJJ). -/
theorem detEquiv_delta (a : Hom K L) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (hK : IsRankZero K) (hL : IsRankZero L) : a.detEquiv ha hqa (delta K hK) = delta L hL := by
  obtain ⟨_, h⟩ := determinantEquivOfSurjectiveQuasiIso_apply_delta K L a ha hqa hL
  exact h

/-- The equivalence of determinant lines `TwoTermComplex.Hom.detEquiv` of a composite is the
composite of the equivalences (Stacks 0FJL). -/
theorem detEquiv_comp (b : Hom L M) (a : Hom K L) (hb : b.IsDegreewiseSurjective)
    (hqb : b.IsQuasiIso) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (hc : (b.comp a).IsDegreewiseSurjective) (hqc : (b.comp a).IsQuasiIso) :
    (b.comp a).detEquiv hc hqc = (a.detEquiv ha hqa).trans (b.detEquiv hb hqb) := by
  obtain ⟨_, h⟩ := determinantEquivOfSurjectiveQuasiIso_comp K L M a b ha hqa hb hqb
  exact h.symm

private theorem eq_algebraMap_algebraMapInv {N : Type*} [AddCommGroup N] [Module R N]
    [Subsingleton N] (z : ExteriorAlgebra R N) :
    z = algebraMap R _ (ExteriorAlgebra.algebraMapInv z) := by
  have h : (Algebra.ofId R (ExteriorAlgebra R N)).comp ExteriorAlgebra.algebraMapInv =
      AlgHom.id R _ := by
    ext m
    simp [Subsingleton.elim m 0]
  exact (DFunLike.congr_fun h z).symm

/-- The equivalence of determinant lines induced by a morphism whose two components are
bijective is conjugation by the determinant maps of the two components. -/
theorem detEquiv_eq_arrowCongr_of_bijective (a : Hom K L) (hn : Function.Bijective a.neg)
    (hz : Function.Bijective a.zero) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) :
    a.detEquiv ha hqa = LinearEquiv.arrowCongr (mapEquiv (LinearEquiv.ofBijective a.neg hn))
      (mapEquiv (LinearEquiv.ofBijective a.zero hz)) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let D := determinantEquivOfSurjectiveQuasiIso K L a ha hqa
  let en := LinearEquiv.ofBijective a.neg hn
  let ez := LinearEquiv.ofBijective a.zero hz
  have : Subsingleton (LinearMap.ker a.neg) :=
    ⟨fun x y => Subtype.ext (hn.1 (x.2.trans y.2.symm))⟩
  refine (D.unique _ fun φ x y => ?_).symm
  set c := ExteriorAlgebra.algebraMapInv (x : ExteriorAlgebra R (LinearMap.ker a.neg))
  have hx : (x : ExteriorAlgebra R (LinearMap.ker a.neg)) = algebraMap R _ c :=
    eq_algebraMap_algebraMapInv _
  set w := (mapEquiv en).symm y
  have hw : ExteriorAlgebra.map a.neg (w : ExteriorAlgebra R K₁) = y :=
    congrArg Subtype.val ((mapEquiv en).apply_symm_apply y)
  have hkn : kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y) = c • w := by
    apply Subtype.ext
    rw [coe_kernelDeterminantEquiv_tmul _ _ x y _ hw, hx, AlgHom.commutes, ← Algebra.smul_def]
    rfl
  rw [hkn, map_smul, LinearEquiv.arrowCongr_apply]
  apply Subtype.ext
  rw [coe_kernelDeterminantEquiv_tmul _ _ _ _ ((φ w : ProjectiveDeterminant.module (M := K₀)) :
    ExteriorAlgebra R K₀) rfl]
  show ExteriorAlgebra.map (LinearMap.ker a.zero).subtype
    (ExteriorAlgebra.map a.kernelDifferential (x : ExteriorAlgebra R _)) * _ = _
  rw [hx, AlgHom.commutes, AlgHom.commutes, ← Algebra.smul_def]
  rfl

/-- The equivalence of determinant lines induced by a morphism whose two components are
bijective, evaluated: `φ ↦ det(a₀) ∘ φ ∘ det(a₋₁)⁻¹`. -/
theorem detEquiv_apply_of_bijective (a : Hom K L) (hn : Function.Bijective a.neg)
    (hz : Function.Bijective a.zero) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (φ : determinantLine K) :
    a.detEquiv ha hqa φ = (mapEquiv (LinearEquiv.ofBijective a.zero hz)).toLinearMap ∘ₗ φ ∘ₗ
      (mapEquiv (LinearEquiv.ofBijective a.neg hn)).symm.toLinearMap := by
  rw [detEquiv_eq_arrowCongr_of_bijective a hn hz]
  rfl

/-- The identity morphism induces the identity of the determinant line. -/
theorem detEquiv_id (K : K₁ →ₗ[R] K₀) (ha : (Hom.id K).IsDegreewiseSurjective)
    (hqa : (Hom.id K).IsQuasiIso) : (Hom.id K).detEquiv ha hqa = LinearEquiv.refl R _ := by
  have hb₁ : Function.Bijective (Hom.id K).neg := ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩
  have hb₀ : Function.Bijective (Hom.id K).zero := ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩
  ext φ x
  rw [detEquiv_eq_arrowCongr_of_bijective _ hb₁ hb₀, LinearEquiv.arrowCongr_apply]
  have hx : (mapEquiv (LinearEquiv.ofBijective _ hb₁)).symm x = x := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    show x.1 = ExteriorAlgebra.map LinearMap.id x.1
    rw [ExteriorAlgebra.map_id, AlgHom.id_apply]
  rw [hx]
  show ExteriorAlgebra.map LinearMap.id (φ x).1 = (φ x).1
  rw [ExteriorAlgebra.map_id, AlgHom.id_apply]

end Hom

end DetEquiv

section DeterminantLine

universe u v₁ v₀ w₁ w₀

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]

/-- The base change of an element of the determinant line of a two-term complex: the base change
of the map of determinants, read through `ProjectiveDeterminant.baseChangeEquiv`. -/
def determinantLineBaseChangeMap (K : K₁ →ₗ[R] K₀) :
    determinantLine K →ₗ[R] determinantLine (K.baseChange A) :=
  ((LinearEquiv.arrowCongr (baseChangeEquiv (R := R) (A := A) (M := K₁))
      (baseChangeEquiv (R := R) (A := A) (M := K₀))).toLinearMap.restrictScalars R) ∘ₗ
    LinearMap.baseChangeHom R A _ _

/-- `TwoTermComplex.determinantLineBaseChangeMap` is the base change of the map of determinants,
conjugated by `ProjectiveDeterminant.baseChangeEquiv`. -/
theorem determinantLineBaseChangeMap_apply (K : K₁ →ₗ[R] K₀) (φ : determinantLine K)
    (x : ProjectiveDeterminant.module (R := A) (M := A ⊗[R] K₁)) :
    determinantLineBaseChangeMap A K φ x =
      baseChangeEquiv (φ.baseChange A (baseChangeEquiv.symm x)) :=
  rfl

/-- `TwoTermComplex.determinantLineBaseChangeMap` on the image of a pure tensor. -/
theorem determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul (K : K₁ →ₗ[R] K₀)
    (φ : determinantLine K) (a : A) (y : ProjectiveDeterminant.module (R := R) (M := K₁)) :
    determinantLineBaseChangeMap A K φ (baseChangeEquiv (a ⊗ₜ[R] y)) =
      baseChangeEquiv (a ⊗ₜ[R] φ y) := by
  rw [determinantLineBaseChangeMap_apply, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul]

/-- The determinant line of a two-term complex commutes with base change. -/
def determinantLineBaseChange (K : K₁ →ₗ[R] K₀) :
    A ⊗[R] determinantLine K ≃ₗ[A] determinantLine (K.baseChange A) :=
  letI := ProjectiveDeterminant.invertible (R := R) (M := K₁)
  (StacksDraft.RelativelyPerfect.linearMap_isBaseChange_of_finite_projective (B := A)
      (ProjectiveDeterminant.module (R := R) (M := K₁))
      (ProjectiveDeterminant.module (R := R) (M := K₀))).equiv.trans
    (LinearEquiv.arrowCongr baseChangeEquiv baseChangeEquiv)

/-- `TwoTermComplex.determinantLineBaseChange` on a pure tensor. -/
theorem determinantLineBaseChange_tmul (K : K₁ →ₗ[R] K₀) (a : A) (φ : determinantLine K) :
    determinantLineBaseChange A K (a ⊗ₜ[R] φ) = a • determinantLineBaseChangeMap A K φ := by
  simp only [determinantLineBaseChange, LinearEquiv.trans_apply, IsBaseChange.equiv_tmul,
    map_smul]
  rfl

/-- A two-term complex of rank zero stays of rank zero after base change. -/
theorem isRankZero_baseChange {K : K₁ →ₗ[R] K₀} (hK : IsRankZero K) :
    IsRankZero (K.baseChange A) := fun p => by
  rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_baseChange]
  exact hK _

/-- The base change of the canonical element of a rank-zero two-term complex is the canonical
element of its base change. -/
theorem determinantLineBaseChangeMap_delta (K : K₁ →ₗ[R] K₀) (hK : IsRankZero K)
    (hK' : IsRankZero (K.baseChange A)) :
    determinantLineBaseChangeMap A K (delta K hK) = delta (K.baseChange A) hK' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨t, rfl⟩ := (baseChangeEquiv (R := R) (A := A) (M := K₁)).surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul a y =>
      rw [determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul]
      exact (map_baseChange_baseChangeEquiv_tmul hK hK' K a y).symm

end DeterminantLine

section MainBaseChange

universe u v₁ v₀ w₁ w₀

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
variable {K : K₁ →ₗ[R] K₀} {L : L₁ →ₗ[R] L₀}

namespace Hom

/-- The canonical element of the kernel complex of a base change is the base change of the
canonical element of the kernel complex. -/
theorem delta_kernelDifferential_baseChange (a : Hom K L) (ha : a.IsDegreewiseSurjective)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
    [Module.Finite A (LinearMap.ker (a.baseChange A).neg)]
    [Module.Projective A (LinearMap.ker (a.baseChange A).neg)]
    [Module.Finite A (LinearMap.ker (a.baseChange A).zero)]
    [Module.Projective A (LinearMap.ker (a.baseChange A).zero)]
    (h : IsRankZero a.kernelDifferential) (h' : IsRankZero (a.baseChange A).kernelDifferential)
    (c : A) (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :
    delta (a.baseChange A).kernelDifferential h'
        (mapEquiv (kernelBaseChangeEquiv A a.neg ha.1) (baseChangeEquiv (c ⊗ₜ[R] x))) =
      mapEquiv (kernelBaseChangeEquiv A a.zero ha.2)
        (baseChangeEquiv (c ⊗ₜ[R] delta a.kernelDifferential h x)) := by
  apply Subtype.ext
  show ExteriorAlgebra.map (a.baseChange A).kernelDifferential
      (ExteriorAlgebra.map (kernelBaseChangeEquiv A a.neg ha.1).toLinearMap
        ((exteriorAlgebraBaseChange R A (LinearMap.ker a.neg)).symm
          (c ⊗ₜ[R] (x : ExteriorAlgebra R (LinearMap.ker a.neg))))) =
    ExteriorAlgebra.map (kernelBaseChangeEquiv A a.zero ha.2).toLinearMap
      ((exteriorAlgebraBaseChange R A (LinearMap.ker a.zero)).symm
        (c ⊗ₜ[R] ExteriorAlgebra.map a.kernelDifferential
          (x : ExteriorAlgebra R (LinearMap.ker a.neg))))
  rw [← map_baseChange_exteriorAlgebraBaseChange_symm_tmul, ← AlgHom.comp_apply,
    ExteriorAlgebra.map_comp_map, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    kernelDifferential_baseChange A a ha]

private theorem compatibility_baseChange_left (a : Hom K L) (ha : a.IsDegreewiseSurjective)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
    [Module.Finite A (LinearMap.ker (a.baseChange A).neg)]
    [Module.Projective A (LinearMap.ker (a.baseChange A).neg)]
    [Module.Finite A (LinearMap.ker (a.baseChange A).zero)]
    [Module.Projective A (LinearMap.ker (a.baseChange A).zero)]
    (hr : IsRankZero a.kernelDifferential) (hr' : IsRankZero (a.baseChange A).kernelDifferential)
    (c : A) (φ : determinantLine L) (a₁ b : A)
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    kernelDeterminantEquiv (a.baseChange A).zero ha.baseChange.2
        (delta (a.baseChange A).kernelDifferential hr'
            (mapEquiv (kernelBaseChangeEquiv A a.neg ha.1) (baseChangeEquiv (a₁ ⊗ₜ[R] x))) ⊗ₜ[A]
          (c • determinantLineBaseChangeMap A L φ) (baseChangeEquiv (b ⊗ₜ[R] y))) =
      c • baseChangeEquiv ((a₁ * b) ⊗ₜ[R]
        kernelDeterminantEquiv a.zero ha.2 (delta a.kernelDifferential hr x ⊗ₜ[R] φ y)) := by
  refine (congrArg (fun z => kernelDeterminantEquiv (a.baseChange A).zero ha.baseChange.2
    (z ⊗ₜ[A] ((c • determinantLineBaseChangeMap A L φ) (baseChangeEquiv (b ⊗ₜ[R] y)))))
    (delta_kernelDifferential_baseChange A a ha hr hr' a₁ x)).trans ?_
  rw [LinearMap.smul_apply, determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul,
    TensorProduct.tmul_smul, map_smul]
  exact congrArg (c • ·) (kernelDeterminantEquiv_baseChange_tmul A a.zero ha.2 ha.baseChange.2 a₁ b
    _ _)

omit [Module.Finite R L₀] [Module.Projective R L₀] in
private theorem compatibility_baseChange_right (a : Hom K L) (ha : a.IsDegreewiseSurjective)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite A (LinearMap.ker (a.baseChange A).neg)]
    [Module.Projective A (LinearMap.ker (a.baseChange A).neg)]
    (c : A) (ψ : determinantLine K) (a₁ b : A)
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    (c • determinantLineBaseChangeMap A K ψ)
        (kernelDeterminantEquiv (a.baseChange A).neg ha.baseChange.1
          (mapEquiv (kernelBaseChangeEquiv A a.neg ha.1) (baseChangeEquiv (a₁ ⊗ₜ[R] x)) ⊗ₜ[A]
            baseChangeEquiv (b ⊗ₜ[R] y))) =
      c • baseChangeEquiv ((a₁ * b) ⊗ₜ[R] ψ (kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y))) := by
  rw [LinearMap.smul_apply]
  exact congrArg (c • ·) ((congrArg _ (kernelDeterminantEquiv_baseChange_tmul A a.neg ha.1
    ha.baseChange.1 a₁ b x y)).trans
      (determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul A K ψ _ _))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem compatibility_baseChange (a : Hom K L) (ha : a.IsDegreewiseSurjective)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
    [Module.Finite A (LinearMap.ker (a.baseChange A).neg)]
    [Module.Projective A (LinearMap.ker (a.baseChange A).neg)]
    [Module.Finite A (LinearMap.ker (a.baseChange A).zero)]
    [Module.Projective A (LinearMap.ker (a.baseChange A).zero)]
    (D : SurjectiveQuasiIsoDeterminantData K L a ha)
    (hr' : IsRankZero (a.baseChange A).kernelDifferential) (c : A) (ψ : determinantLine K)
    (x : ProjectiveDeterminant.module (R := A) (M := LinearMap.ker (a.baseChange A).neg))
    (y : ProjectiveDeterminant.module (R := A) (M := A ⊗[R] L₁)) :
    kernelDeterminantEquiv (a.baseChange A).zero ha.baseChange.2
        (delta (a.baseChange A).kernelDifferential hr' x ⊗ₜ[A]
          (c • determinantLineBaseChangeMap A L (D.equiv ψ)) y) =
      (c • determinantLineBaseChangeMap A K ψ)
        (kernelDeterminantEquiv (a.baseChange A).neg ha.baseChange.1 (x ⊗ₜ[A] y)) := by
  obtain ⟨x', rfl⟩ := (mapEquiv (N := LinearMap.ker (a.neg.baseChange A))
    (kernelBaseChangeEquiv A a.neg ha.1)).surjective x
  obtain ⟨u, rfl⟩ := (baseChangeEquiv (R := R) (A := A)
    (M := LinearMap.ker a.neg)).surjective x'
  obtain ⟨v, rfl⟩ := (baseChangeEquiv (R := R) (A := A) (M := L₁)).surjective y
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul]
  | add u u' hu hu' =>
      simp only [LinearEquiv.map_add, LinearMap.map_add, TensorProduct.add_tmul]
      rw [hu, hu']
  | tmul a₁ x₀ =>
      induction v using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.tmul_zero]
      | add v v' hv hv' =>
          simp only [LinearEquiv.map_add, LinearMap.map_add, TensorProduct.tmul_add]
          rw [hv, hv']
      | tmul b y₀ =>
          refine (compatibility_baseChange_left A a ha D.kernelRankZero hr' c (D.equiv ψ) a₁ b
            x₀ y₀).trans ?_
          refine (congrArg (fun t : ProjectiveDeterminant.module (R := R) (M := K₀) =>
            c • baseChangeEquiv (R := R) (A := A) (M := K₀) ((a₁ * b) ⊗ₜ[R] t))
              (D.compatibility ψ x₀ y₀)).trans ?_
          exact (compatibility_baseChange_right A a ha c ψ a₁ b x₀ y₀).symm

set_option synthInstance.maxHeartbeats 200000 in
/-- **The equivalence of determinant lines of a degreewise-surjective quasi-isomorphism commutes
with base change.** -/
theorem detEquiv_baseChange (a : Hom K L) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (φ : determinantLine K) :
    (a.baseChange A).detEquiv ha.baseChange (hqa.baseChange A ha)
        (determinantLineBaseChangeMap A K φ) =
      determinantLineBaseChangeMap A L (a.detEquiv ha hqa φ) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let : Module.Finite A (LinearMap.ker (a.baseChange A).neg) :=
    kernel_finite _ ha.baseChange.1
  let : Module.Projective A (LinearMap.ker (a.baseChange A).neg) :=
    kernel_projective _ ha.baseChange.1
  let : Module.Finite A (LinearMap.ker (a.baseChange A).zero) :=
    kernel_finite _ ha.baseChange.2
  let : Module.Projective A (LinearMap.ker (a.baseChange A).zero) :=
    kernel_projective _ ha.baseChange.2
  let D := determinantEquivOfSurjectiveQuasiIso K L a ha hqa
  let D' := determinantEquivOfSurjectiveQuasiIso (K.baseChange A) (L.baseChange A)
    (a.baseChange A) ha.baseChange (hqa.baseChange A ha)
  let e : determinantLine (K.baseChange A) ≃ₗ[A] determinantLine (L.baseChange A) :=
    (determinantLineBaseChange A K).symm ≪≫ₗ LinearEquiv.baseChange R A _ _ D.equiv ≪≫ₗ
      determinantLineBaseChange A L
  have he (c : A) (ψ : determinantLine K) :
      e (c • determinantLineBaseChangeMap A K ψ) =
        c • determinantLineBaseChangeMap A L (D.equiv ψ) := by
    rw [← determinantLineBaseChange_tmul, ← determinantLineBaseChange_tmul]
    simp [e]
  have hD' : D'.equiv = e := by
    refine (D'.unique e fun ψ x y => ?_).symm
    obtain ⟨t, rfl⟩ := (determinantLineBaseChange A K).surjective ψ
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t t' ht ht' =>
        simp only [map_add, LinearMap.add_apply, TensorProduct.tmul_add, ht, ht']
    | tmul c ψ =>
        rw [determinantLineBaseChange_tmul, he]
        exact compatibility_baseChange A a ha D _ c ψ x y
  show D'.equiv _ = _
  rw [hD']
  simpa using he 1 φ

end Hom

/-- **The equivalence of determinant lines of a degreewise-surjective quasi-isomorphism commutes
with base change**, in the spelling of `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso`. -/
theorem determinantEquivOfSurjectiveQuasiIso_baseChange (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀)
    (a : Hom K L) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) (φ : determinantLine K) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    letI : Module.Finite A (LinearMap.ker (a.baseChange A).neg) :=
      kernel_finite _ ha.baseChange.1
    letI : Module.Projective A (LinearMap.ker (a.baseChange A).neg) :=
      kernel_projective _ ha.baseChange.1
    letI : Module.Finite A (LinearMap.ker (a.baseChange A).zero) :=
      kernel_finite _ ha.baseChange.2
    letI : Module.Projective A (LinearMap.ker (a.baseChange A).zero) :=
      kernel_projective _ ha.baseChange.2
    (determinantEquivOfSurjectiveQuasiIso (K.baseChange A) (L.baseChange A) (a.baseChange A)
        ha.baseChange (hqa.baseChange A ha)).equiv (determinantLineBaseChangeMap A K φ) =
      determinantLineBaseChangeMap A L
        ((determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv φ) :=
  a.detEquiv_baseChange A ha hqa φ

end MainBaseChange

section Tower

universe u v₁ v₀

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (A' : Type u) [CommRing A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
variable {K₁ : Type v₁} {K₀ : Type v₀}
variable [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]

namespace Hom

/-- The comparison `A' ⊗_A (A ⊗_R K) ≅ A' ⊗_R K` of base changes of a two-term complex along a
tower `R → A → A'`, given by `TensorProduct.AlgebraTensorModule.cancelBaseChange` in each
degree. -/
def cancelBaseChange (K : K₁ →ₗ[R] K₀) :
    Hom ((K.baseChange A).baseChange A') (K.baseChange A') where
  neg := (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' K₁).toLinearMap
  zero := (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' K₀).toLinearMap
  comm := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul a' t =>
        induction t using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.tmul_zero, map_zero]
        | add t t' ht ht' => simp only [TensorProduct.tmul_add, map_add, ht, ht']
        | tmul a k => simp

/-- The comparison `R ⊗_R K ≅ K` of the base change of a two-term complex along the identity of
`R`, given by `TensorProduct.lid` in each degree. -/
def lid (K : K₁ →ₗ[R] K₀) : Hom (K.baseChange R) K where
  neg := (TensorProduct.lid R K₁).toLinearMap
  zero := (TensorProduct.lid R K₀).toLinearMap
  comm := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul r k => simp

/-- `TwoTermComplex.Hom.cancelBaseChange` is bijective in degree `-1`. -/
theorem bijective_cancelBaseChange_neg (K : K₁ →ₗ[R] K₀) :
    Function.Bijective (cancelBaseChange A A' K).neg :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' K₁).bijective

/-- `TwoTermComplex.Hom.cancelBaseChange` is bijective in degree `0`. -/
theorem bijective_cancelBaseChange_zero (K : K₁ →ₗ[R] K₀) :
    Function.Bijective (cancelBaseChange A A' K).zero :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A' A' K₀).bijective

/-- `TwoTermComplex.Hom.lid` is bijective in degree `-1`. -/
theorem bijective_lid_neg (K : K₁ →ₗ[R] K₀) : Function.Bijective (lid K).neg :=
  (TensorProduct.lid R K₁).bijective

/-- `TwoTermComplex.Hom.lid` is bijective in degree `0`. -/
theorem bijective_lid_zero (K : K₁ →ₗ[R] K₀) : Function.Bijective (lid K).zero :=
  (TensorProduct.lid R K₀).bijective

variable [Module.Finite R K₁] [Module.Projective R K₁] [Module.Finite R K₀]
  [Module.Projective R K₀]

private theorem detEquiv_cancelBaseChange_tmul (K : K₁ →ₗ[R] K₀) (φ : determinantLine K)
    (a : A) (a' : A') (x : ProjectiveDeterminant.module (R := R) (M := K₁)) :
    mapEquiv (LinearEquiv.ofBijective _ (bijective_cancelBaseChange_zero A A' K))
        (determinantLineBaseChangeMap A' (K.baseChange A) (determinantLineBaseChangeMap A K φ)
          (baseChangeEquiv (a' ⊗ₜ[A] baseChangeEquiv (a ⊗ₜ[R] x)))) =
      determinantLineBaseChangeMap A' K φ
        (mapEquiv (LinearEquiv.ofBijective _ (bijective_cancelBaseChange_neg A A' K))
          (baseChangeEquiv (a' ⊗ₜ[A] baseChangeEquiv (a ⊗ₜ[R] x)))) := by
  rw [determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul,
    determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul]
  refine (mapEquiv_cancelBaseChange_baseChangeEquiv_tmul A A' a a' (φ x)).trans ?_
  refine (determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul A' K φ (a • a') x).symm.trans ?_
  exact congrArg _ (mapEquiv_cancelBaseChange_baseChangeEquiv_tmul A A' a a' x).symm

/-- **Transitivity of the base change of determinant lines** along a tower `R → A → A'`: base
changing along `R → A` and then along `A → A'` is base changing along `R → A'`, read through the
comparison `A' ⊗_A (A ⊗_R K) ≅ A' ⊗_R K`. -/
theorem detEquiv_cancelBaseChange (K : K₁ →ₗ[R] K₀)
    (ha : (cancelBaseChange A A' K).IsDegreewiseSurjective)
    (hqa : (cancelBaseChange A A' K).IsQuasiIso) (φ : determinantLine K) :
    (cancelBaseChange A A' K).detEquiv ha hqa
        (determinantLineBaseChangeMap A' (K.baseChange A) (determinantLineBaseChangeMap A K φ)) =
      determinantLineBaseChangeMap A' K φ := by
  rw [detEquiv_eq_arrowCongr_of_bijective _ (bijective_cancelBaseChange_neg A A' K)
    (bijective_cancelBaseChange_zero A A' K)]
  refine LinearMap.ext fun y => ?_
  rw [LinearEquiv.arrowCongr_apply]
  obtain ⟨y, rfl⟩ := (mapEquiv (LinearEquiv.ofBijective _
    (bijective_cancelBaseChange_neg A A' K))).surjective y
  rw [LinearEquiv.symm_apply_apply]
  obtain ⟨t, rfl⟩ := (baseChangeEquiv (R := A) (A := A') (M := A ⊗[R] K₁)).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul a' w =>
      obtain ⟨s, rfl⟩ := (baseChangeEquiv (R := R) (A := A) (M := K₁)).surjective w
      induction s using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.tmul_zero]
      | add s s' hs hs' => simp only [map_add, TensorProduct.tmul_add, hs, hs']
      | tmul a x => exact detEquiv_cancelBaseChange_tmul A A' K φ a a' x

/-- The base change of determinant lines along the identity of `R` is the identity, read through
the comparison `R ⊗_R K ≅ K`. -/
theorem detEquiv_lid (K : K₁ →ₗ[R] K₀) (ha : (lid K).IsDegreewiseSurjective)
    (hqa : (lid K).IsQuasiIso) (φ : determinantLine K) :
    (lid K).detEquiv ha hqa (determinantLineBaseChangeMap R K φ) = φ := by
  rw [detEquiv_eq_arrowCongr_of_bijective _ (bijective_lid_neg K) (bijective_lid_zero K)]
  refine LinearMap.ext fun y => ?_
  rw [LinearEquiv.arrowCongr_apply]
  obtain ⟨y, rfl⟩ := (mapEquiv (LinearEquiv.ofBijective _ (bijective_lid_neg K))).surjective y
  rw [LinearEquiv.symm_apply_apply]
  obtain ⟨t, rfl⟩ := (baseChangeEquiv (R := R) (A := R) (M := K₁)).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul r x =>
      rw [determinantLineBaseChangeMap_apply_baseChangeEquiv_tmul]
      refine (mapEquiv_lid_baseChangeEquiv_tmul r (φ x)).trans ?_
      refine (map_smul φ r x).symm.trans ?_
      exact congrArg φ (mapEquiv_lid_baseChangeEquiv_tmul r x).symm

end Hom

end Tower

end TwoTermComplex
