module

public import StacksFrontier.Cotangent.Resolution
public import StacksFrontier.Cotangent.TorTwoMulKernelFunctoriality

/-!
# `Coker(Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B))` does not depend on the resolution

Let `ε : P_• → B` be a resolution of `B` over `A` (Stacks Remark 08QI), `J_n = Ker(P_n → B)` and
read `Tor₂^{P_n}(B, B)` in the tensor-kernel model `Ker(J_n ⊗_{P_n} J_n → J_n²)`
(`Stacks.Cotangent.torTwoSelfIsoMulKernel`). The face maps `d₀, d₁ : P₁ → P₀` lie over `B`, so they
induce `d₀ - d₁ : Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B)`, and Stacks Remark 09D6 identifies
`H₂(L_{B/A})` with its cokernel. That cokernel is `H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` computed by the
resolution `P_•` (Stacks Remark 08QI: `Lπ_!ℱ = ℱ(P_•)`), so it is independent of the resolution;
this file proves that independence directly, for the two lowest terms:

* `P₀ → B` is surjective and `(d₀, d₁) : P₁ → P₀ ×_B P₀` is surjective
  (`exists_faces_eq_of_isResolution`), because the Moore complex of `P_• → B` is a
  quasi-isomorphism;
* a polynomial algebra lifts along a surjection, so for two resolutions `P_•`, `Q_•` there is a map
  `P₀ → Q₀` over `B`, and any two such maps, as well as the two composites `P₁ ⇉ P₀ → Q₀`, are
  joined through `Q₁`.

Hence any `P₀ → Q₀` over `B` induces the same map of cokernels, and these maps compose, so they
are inverse isomorphisms (`torTwoCokerIso`).

## Main definitions

* `Stacks.Cotangent.TorTwo.Resolution.torTwo`: the model of `Tor₂^{P_n}(B, B)` as a `B`-module.
* `Stacks.Cotangent.TorTwo.Resolution.torTwoFace`: `d₀ - d₁ : Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B)`.
* `Stacks.Cotangent.TorTwo.Resolution.torTwoCoker`: its cokernel.
* `Stacks.Cotangent.TorTwo.Resolution.torTwoCokerIso`: the canonical isomorphism between the
  cokernels of two resolutions.

## References

* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v

namespace Stacks.Cotangent.TorTwo.Resolution

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {P : SimplicialObject (CommAlgCat.{v} A)}
  (ε : P ⟶ (SimplicialObject.const _).obj (CommAlgCat.of A B))

/-- An augmentation to a constant simplicial algebra which is surjective in degree zero is
surjective in every degree. -/
theorem surjective_app_of_surjective_zero
    (hε : Function.Surjective (ε.app (op ⦋0⦌)).hom) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (ε.app n).hom := by
  intro b
  obtain ⟨p, hp⟩ := hε b
  let g : op ⦋0⦌ ⟶ n := op (SimplexCategory.const n.unop ⦋0⦌ 0)
  refine ⟨(P.map g).hom p, ?_⟩
  have h := congrArg (fun k => k.hom p) (ε.naturality g)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
    CommAlgCat.hom_comp] at h
  exact h.trans hp

/-- The augmentation of a resolution is surjective in every degree. -/
theorem surjective_app_of_isResolution (hres : CommAlgCat.IsResolution A B P ε)
    (n : SimplexCategoryᵒᵖ) : Function.Surjective (ε.app n).hom :=
  surjective_app_of_surjective_zero ε
    (SSet.surjective_app_zero_of_trivialKanFibrations hres.trivialKanFibration) n

/-- The forgetful functor from commutative `A`-algebras to abelian groups. -/
abbrev toAb : CommAlgCat.{v} A ⥤ AddCommGrpCat.{v} :=
  forget₂ (CommAlgCat.{v} A) (AlgCat.{v} A) ⋙ forget₂ (AlgCat.{v} A) (ModuleCat.{v} A) ⋙
    forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}

/-- A map of chain complexes of abelian groups which is a quasi-isomorphism in degree `0`: an
element of `K₀` mapping to zero is a boundary. -/
theorem exists_d_eq_of_quasiIsoAt_zero {K L : ChainComplex AddCommGrpCat.{v} ℕ} (F : K ⟶ L)
    [QuasiIsoAt F 0] (x : K.X 0) (hx0 : F.f 0 x = 0) : ∃ y : K.X 1, K.d 1 0 y = x := by
  have hhom : IsIso (HomologicalComplex.homologyMap F 0) :=
    (quasiIsoAt_iff_isIso_homologyMap F 0).1 inferInstance
  have hop : HomologicalComplex.opcyclesMap F 0 =
      K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap F 0 ≫ L.isoHomologyι₀.hom := by
    rw [← Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hiso : IsIso (HomologicalComplex.opcyclesMap F 0) := by
    rw [hop]
    infer_instance
  have hinj : Function.Injective (HomologicalComplex.opcyclesMap F 0) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hx : K.pOpcycles 0 x = 0 := by
    apply hinj
    rw [map_zero, ← ConcreteCategory.comp_apply, HomologicalComplex.p_opcyclesMap,
      ConcreteCategory.comp_apply, hx0, map_zero]
  exact (ShortComplex.ab_exact_iff _).1 (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (K.d 1 0) (K.pOpcycles 0) (K.d_pOpcycles 1 0))
    (K.opcyclesIsCokernel 1 0 (by simp))) x hx

/-- The Moore complex of a resolution is exact at `P₀` relative to `B`: an element of `P₀` with
zero image in `B` is `d₀ c - d₁ c` for some `c ∈ P₁`. -/
theorem exists_faces_sub_of_isResolution (hres : CommAlgCat.IsResolution A B P ε)
    (x : P.obj (op ⦋0⦌)) (hx0 : (ε.app (op ⦋0⦌)).hom x = 0) :
    ∃ c : P.obj (op ⦋1⦌), (P.δ (0 : Fin 2)).hom c - (P.δ (1 : Fin 2)).hom c = x := by
  have htfae := CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae A B P ε
    hres.isPolynomialAlgebra (surjective_app_of_isResolution ε hres)
  have hq : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{v}).map
      (Functor.whiskerRight ε (toAb (A := A)))) := (htfae.out 1 2).1 hres
  obtain ⟨y, hy⟩ := exists_d_eq_of_quasiIsoAt_zero
    ((alternatingFaceMapComplex AddCommGrpCat.{v}).map (Functor.whiskerRight ε (toAb (A := A))))
    x hx0
  refine ⟨y, ?_⟩
  rw [← hy]
  show _ = (AlternatingFaceMapComplex.obj (P ⋙ toAb)).d (0 + 1) 0 y
  rw [AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_smul,
    Nat.one_mod, pow_one, neg_smul, AddCommGrpCat.hom_add, AddCommGrpCat.hom_neg,
    AddMonoidHom.add_apply, AddMonoidHom.neg_apply, sub_eq_add_neg]
  rfl

/-- **`(d₀, d₁) : P₁ → P₀ ×_B P₀` is surjective for a resolution.** -/
theorem exists_faces_eq_of_isResolution (hres : CommAlgCat.IsResolution A B P ε)
    {a b : P.obj (op ⦋0⦌)} (h : (ε.app (op ⦋0⦌)).hom a = (ε.app (op ⦋0⦌)).hom b) :
    ∃ c : P.obj (op ⦋1⦌), (P.δ (0 : Fin 2)).hom c = a ∧ (P.δ (1 : Fin 2)).hom c = b := by
  obtain ⟨y, hy⟩ := exists_faces_sub_of_isResolution ε hres (a - b) (by rw [map_sub, h, sub_self])
  have h0 : ∀ z, (P.δ (0 : Fin 2)).hom ((P.σ (0 : Fin 1)).hom z) = z := fun z =>
    congrArg (fun k => k.hom z) (SimplicialObject.δ_comp_σ_self P (n := 0) (i := 0))
  have h1 : ∀ z, (P.δ (1 : Fin 2)).hom ((P.σ (0 : Fin 1)).hom z) = z := fun z =>
    congrArg (fun k => k.hom z) (SimplicialObject.δ_comp_σ_succ P (n := 0) (i := 0))
  refine ⟨y - (P.σ (0 : Fin 1)).hom ((P.δ (1 : Fin 2)).hom y) + (P.σ (0 : Fin 1)).hom b, ?_, ?_⟩
  · rw [map_add, map_sub, h0, h0, ← sub_add_cancel a b, ← hy]
  · rw [map_add, map_sub, h1, h1]
    abel

/-! ### Lifting polynomial algebras -/

section Lift

variable {R : CommAlgCat.{v} A} {S S₁ T : Type*} [CommRing S] [Algebra A S] [CommRing S₁]
  [Algebra A S₁] [CommRing T] [Algebra A T]

/-- A polynomial `A`-algebra lifts along a surjection of `A`-algebras. -/
theorem exists_lift_of_isPolynomialAlgebra (hR : CommAlgCat.IsPolynomialAlgebra A R)
    (g : S →ₐ[A] T) (hg : Function.Surjective g) (h : R →ₐ[A] T) :
    ∃ φ : R →ₐ[A] S, g.comp φ = h := by
  obtain ⟨ι, ⟨e⟩⟩ := hR
  refine ⟨(MvPolynomial.aeval fun i => Function.surjInv hg (h (e (MvPolynomial.X i)))).comp
    e.symm.toAlgHom, (AlgHom.cancel_right (f := e.toAlgHom) e.surjective).1
    (MvPolynomial.algHom_ext fun i => by simp [Function.surjInv_eq hg])⟩

/-- Two maps from a polynomial algebra into `S` that agree after `S → T` are joined through any
`S₁` mapping onto `S ×_T S`. -/
theorem exists_pairLift_of_isPolynomialAlgebra (hR : CommAlgCat.IsPolynomialAlgebra A R)
    (d₀ d₁ : S₁ →ₐ[A] S) (g : S →ₐ[A] T)
    (hpair : ∀ a b : S, g a = g b → ∃ c : S₁, d₀ c = a ∧ d₁ c = b) (φ φ' : R →ₐ[A] S)
    (h : g.comp φ = g.comp φ') : ∃ ψ : R →ₐ[A] S₁, d₀.comp ψ = φ ∧ d₁.comp ψ = φ' := by
  obtain ⟨ι, ⟨e⟩⟩ := hR
  have hc : ∀ i, ∃ c : S₁, d₀ c = φ (e (MvPolynomial.X i)) ∧ d₁ c = φ' (e (MvPolynomial.X i)) :=
    fun i => hpair _ _ (by rw [← AlgHom.comp_apply, h, AlgHom.comp_apply])
  choose c hc₀ hc₁ using hc
  exact ⟨(MvPolynomial.aeval c).comp e.symm.toAlgHom,
    (AlgHom.cancel_right (f := e.toAlgHom) e.surjective).1
      (MvPolynomial.algHom_ext fun i => by simp [hc₀]),
    (AlgHom.cancel_right (f := e.toAlgHom) e.surjective).1
      (MvPolynomial.algHom_ext fun i => by simp [hc₁])⟩

end Lift

/-! ### Maps of cokernels induced by maps over `B` -/

section Coker

variable {P₀ P₁ Q₀ Q₁ : Type*} [CommRing P₀] [CommRing P₁] [CommRing Q₀] [CommRing Q₁]
  {εP : P₀ →+* B} {εQ : Q₀ →+* B} {εP₁ : P₁ →+* B} {εQ₁ : Q₁ →+* B}
  [Fact (Function.Surjective εP)] [Fact (Function.Surjective εQ)]
  [Fact (Function.Surjective εP₁)] [Fact (Function.Surjective εQ₁)]
  {dP₀ dP₁ : P₁ →+* P₀} {dQ₀ dQ₁ : Q₁ →+* Q₀}
  (hP₀ : εP.comp dP₀ = εP₁) (hP₁ : εP.comp dP₁ = εP₁)
  (hQ₀ : εQ.comp dQ₀ = εQ₁) (hQ₁ : εQ.comp dQ₁ = εQ₁)

/-- `d₀ - d₁` on the model of `Tor₂`, for a pair of ring maps over `B`. -/
def faceDiff (d₀ d₁ : P₁ →+* P₀) (h₀ : εP.comp d₀ = εP₁) (h₁ : εP.comp d₁ = εP₁) :
    mulKernel εP₁ →ₗ[B] mulKernel εP :=
  mulKernelMap d₀ h₀ - mulKernelMap d₁ h₁

/-- If `ψ : P₁ → Q₁` lies over `φ : P₀ → Q₀` for both faces, `φ` maps the image of `d₀ - d₁` for
`P` into that for `Q`. -/
theorem mulKernelMap_faceDiff (φ : P₀ →+* Q₀) (hφ : εQ.comp φ = εP) (ψ : P₁ →+* Q₁)
    (hψ : εQ₁.comp ψ = εP₁) (h₀ : dQ₀.comp ψ = φ.comp dP₀) (h₁ : dQ₁.comp ψ = φ.comp dP₁)
    (k : mulKernel εP₁) :
    mulKernelMap φ hφ (faceDiff dP₀ dP₁ hP₀ hP₁ k) =
      faceDiff dQ₀ dQ₁ hQ₀ hQ₁ (mulKernelMap ψ hψ k) := by
  simp only [faceDiff, LinearMap.sub_apply, map_sub]
  rw [← mulKernelMap_comp, ← mulKernelMap_comp, ← mulKernelMap_comp, ← mulKernelMap_comp,
    mulKernelMap_congr h₀.symm, mulKernelMap_congr h₁.symm]

/-- Two maps `P₀ → Q₀` over `B` joined through `Q₁` agree modulo the image of `d₀ - d₁`. -/
theorem mulKernelMap_sub_mulKernelMap (φ φ' : P₀ →+* Q₀) (hφ : εQ.comp φ = εP)
    (hφ' : εQ.comp φ' = εP) (χ : P₀ →+* Q₁) (hχ : εQ₁.comp χ = εP) (h₀ : dQ₀.comp χ = φ)
    (h₁ : dQ₁.comp χ = φ') (k : mulKernel εP) :
    mulKernelMap φ hφ k - mulKernelMap φ' hφ' k =
      faceDiff dQ₀ dQ₁ hQ₀ hQ₁ (mulKernelMap χ hχ k) := by
  simp only [faceDiff, LinearMap.sub_apply]
  rw [← mulKernelMap_comp, ← mulKernelMap_comp, mulKernelMap_congr h₀.symm,
    mulKernelMap_congr h₁.symm]

end Coker

/-! ### The cokernel of `d₀ - d₁` for a resolution -/

section OfResolution

/-- The augmentation `P_n → B` of a resolution, as a ring map. -/
def aug (n : ℕ) : P.obj (op ⦋n⦌) →+* B := (ε.app (op ⦋n⦌)).hom.toRingHom

/-- The face map `d_i : P₁ → P₀`, as a ring map. -/
def face (i : Fin 2) : P.obj (op ⦋1⦌) →+* P.obj (op ⦋0⦌) := (P.δ i).hom.toRingHom

/-- Each face map `d_i : P₁ → P₀` lies over `B`. -/
theorem aug_comp_face (i : Fin 2) : (aug ε 0).comp (face (P := P) i) = aug ε 1 := by
  have h := ε.naturality (SimplexCategory.δ i).op
  ext y
  exact congrArg (fun f => f.hom y) h

variable {ε} (hres : CommAlgCat.IsResolution A B P ε)

include hres in
/-- The augmentation `P_n → B` of a resolution is surjective. -/
theorem aug_surjective (n : ℕ) : Function.Surjective (aug ε n) :=
  surjective_app_of_isResolution ε hres (op ⦋n⦌)

/-- **The model `Ker(J_n ⊗_{P_n} J_n → J_n²)` of `Tor₂^{P_n}(B, B)`**, as a `B`-module. -/
def torTwo (n : ℕ) : ModuleCat.{v} B :=
  have : Fact (Function.Surjective (aug ε n)) := ⟨aug_surjective hres n⟩
  ModuleCat.of B (mulKernel (aug ε n))

/-- **`d₀ - d₁ : Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B)`** for the face maps of the resolution. -/
def torTwoFace : torTwo hres 1 ⟶ torTwo hres 0 :=
  have : Fact (Function.Surjective (aug ε 0)) := ⟨aug_surjective hres 0⟩
  have : Fact (Function.Surjective (aug ε 1)) := ⟨aug_surjective hres 1⟩
  ModuleCat.ofHom (faceDiff (face 0) (face 1) (aug_comp_face ε 0) (aug_comp_face ε 1))

/-- **`Coker(Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B))`**, the cokernel of `d₀ - d₁`. -/
def torTwoCoker : ModuleCat.{v} B :=
  ModuleCat.of B ((torTwo hres 0) ⧸ LinearMap.range (torTwoFace hres).hom)

end OfResolution

/-! ### Independence of the resolution -/

section Transfer

variable {ε} {Q R : SimplicialObject (CommAlgCat.{v} A)}
  {εQ : Q ⟶ (SimplicialObject.const _).obj (CommAlgCat.of A B)}
  {εR : R ⟶ (SimplicialObject.const _).obj (CommAlgCat.of A B)}
  (hP : CommAlgCat.IsResolution A B P ε) (hQ : CommAlgCat.IsResolution A B Q εQ)
  (hR : CommAlgCat.IsResolution A B R εR)

/-- The map `φ : P₀ → Q₀` of `A`-algebras lies over `B`. -/
def IsLift (φ : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌)) : Prop :=
  (aug εQ 0).comp φ.toRingHom = aug ε 0

/-- A map out of a polynomial algebra into `Q₁`, whose two faces are prescribed maps into `Q₀`
that agree over `B`. -/
private theorem exists_comp_face_eq (hQ : CommAlgCat.IsResolution A B Q εQ)
    {X : CommAlgCat.{v} A} (hX : CommAlgCat.IsPolynomialAlgebra A X) (φ φ' : X →ₐ[A] Q.obj (op ⦋0⦌))
    (h : ∀ y, aug εQ 0 (φ y) = aug εQ 0 (φ' y)) :
    ∃ ψ : X →ₐ[A] Q.obj (op ⦋1⦌), (face 0).comp ψ.toRingHom = φ.toRingHom ∧
      (face 1).comp ψ.toRingHom = φ'.toRingHom := by
  obtain ⟨ψ, hψ₀, hψ₁⟩ := exists_pairLift_of_isPolynomialAlgebra hX (Q.δ (0 : Fin 2)).hom
    (Q.δ (1 : Fin 2)).hom (εQ.app (op ⦋0⦌)).hom
    (fun a b h => exists_faces_eq_of_isResolution εQ hQ h) _ _ (AlgHom.ext h)
  exact ⟨ψ, RingHom.ext (AlgHom.congr_fun hψ₀), RingHom.ext (AlgHom.congr_fun hψ₁)⟩

include hP hQ in
/-- For two resolutions `P_•` and `Q_•` of `B`, there is a map `P₀ → Q₀` of `A`-algebras over
`B`. -/
theorem exists_isLift :
    ∃ φ : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌), IsLift (ε := ε) (εQ := εQ) φ := by
  obtain ⟨φ, hφ⟩ := exists_lift_of_isPolynomialAlgebra (hP.isPolynomialAlgebra (op ⦋0⦌))
    (εQ.app (op ⦋0⦌)).hom (aug_surjective hQ 0) (ε.app (op ⦋0⦌)).hom
  exact ⟨φ, RingHom.ext fun x => congrArg (fun f => f x) hφ⟩

/-- The map of models of `Tor₂^{P₀}(B, B) → Tor₂^{Q₀}(B, B)` induced by a lift. -/
def liftMap (φ : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌)) (hφ : IsLift (ε := ε) (εQ := εQ) φ) :
    torTwo hP 0 ⟶ torTwo hQ 0 :=
  have : Fact (Function.Surjective (aug ε 0)) := ⟨aug_surjective hP 0⟩
  have : Fact (Function.Surjective (aug εQ 0)) := ⟨aug_surjective hQ 0⟩
  ModuleCat.ofHom (mulKernelMap φ.toRingHom hφ)

/-- The map induced by a lift `P₀ → Q₀` sends the image of `d₀ - d₁` for `P` into the image of
`d₀ - d₁` for `Q`. -/
theorem range_torTwoFace_le (φ : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌))
    (hφ : IsLift (ε := ε) (εQ := εQ) φ) :
    LinearMap.range (torTwoFace hP).hom ≤
      (LinearMap.range (torTwoFace hQ).hom).comap (liftMap hP hQ φ hφ).hom := by
  have : Fact (Function.Surjective (aug ε 0)) := ⟨aug_surjective hP 0⟩
  have : Fact (Function.Surjective (aug ε 1)) := ⟨aug_surjective hP 1⟩
  have : Fact (Function.Surjective (aug εQ 0)) := ⟨aug_surjective hQ 0⟩
  have : Fact (Function.Surjective (aug εQ 1)) := ⟨aug_surjective hQ 1⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨ψ, hψ₀', hψ₁'⟩ := exists_comp_face_eq hQ (hP.isPolynomialAlgebra (op ⦋1⦌))
    (φ.comp (P.δ (0 : Fin 2)).hom) (φ.comp (P.δ (1 : Fin 2)).hom) fun y =>
      (RingHom.congr_fun hφ (face 0 y)).trans <|
        (RingHom.congr_fun (aug_comp_face ε 0) y).trans <|
        (RingHom.congr_fun (aug_comp_face ε 1) y).symm.trans
          (RingHom.congr_fun hφ (face 1 y)).symm
  change _ = φ.toRingHom.comp (face 0) at hψ₀'
  change _ = φ.toRingHom.comp (face 1) at hψ₁'
  have hψ : (aug εQ 1).comp ψ.toRingHom = aug ε 1 := by
    rw [← aug_comp_face εQ 0, RingHom.comp_assoc, hψ₀', ← RingHom.comp_assoc, hφ]
    exact aug_comp_face ε 0
  exact ⟨mulKernelMap ψ.toRingHom hψ x, (mulKernelMap_faceDiff (aug_comp_face ε 0)
    (aug_comp_face ε 1) (aug_comp_face εQ 0) (aug_comp_face εQ 1) φ.toRingHom hφ ψ.toRingHom hψ
    hψ₀' hψ₁' x).symm⟩

/-- Maps out of the cokernel of `d₀ - d₁` are equal if they agree on classes. -/
private theorem torTwoCoker_hom_ext (hP : CommAlgCat.IsResolution A B P ε) {X : ModuleCat.{v} B}
    (f g : torTwoCoker hP ⟶ X)
    (h : ∀ k : torTwo hP 0, f.hom (Submodule.Quotient.mk k) = g.hom (Submodule.Quotient.mk k)) :
    f = g := by
  ext c
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact h k

/-- The map of cokernels induced by a lift. -/
def cokerMapOfLift (φ : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌)) (hφ : IsLift (ε := ε) (εQ := εQ) φ) :
    torTwoCoker hP ⟶ torTwoCoker hQ :=
  ModuleCat.ofHom (Submodule.mapQ _ _ (liftMap hP hQ φ hφ).hom (range_torTwoFace_le hP hQ φ hφ))

/-- The map of cokernels induced by a lift sends the class of `k` to the class of its image. -/
theorem cokerMapOfLift_mk (φ : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌))
    (hφ : IsLift (ε := ε) (εQ := εQ) φ) (k : torTwo hP 0) :
    (cokerMapOfLift hP hQ φ hφ).hom (Submodule.Quotient.mk k) =
      Submodule.Quotient.mk ((liftMap hP hQ φ hφ).hom k) := rfl

/-- **Any two lifts induce the same map of cokernels.** -/
theorem cokerMapOfLift_eq (φ φ' : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌))
    (hφ : IsLift (ε := ε) (εQ := εQ) φ) (hφ' : IsLift (ε := ε) (εQ := εQ) φ') :
    cokerMapOfLift hP hQ φ hφ = cokerMapOfLift hP hQ φ' hφ' := by
  have : Fact (Function.Surjective (aug ε 0)) := ⟨aug_surjective hP 0⟩
  have : Fact (Function.Surjective (aug εQ 0)) := ⟨aug_surjective hQ 0⟩
  have : Fact (Function.Surjective (aug εQ 1)) := ⟨aug_surjective hQ 1⟩
  obtain ⟨χ, hχ₀', hχ₁'⟩ := exists_comp_face_eq hQ (hP.isPolynomialAlgebra (op ⦋0⦌)) φ φ'
    fun y => (congrArg (fun f => f y) hφ).trans (congrArg (fun f => f y) hφ').symm
  have hχ : (aug εQ 1).comp χ.toRingHom = aug ε 0 := by
    rw [← aug_comp_face εQ 0, RingHom.comp_assoc, hχ₀', hφ]
  refine torTwoCoker_hom_ext hP _ _ fun k => ?_
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  exact ⟨mulKernelMap χ.toRingHom hχ k, (mulKernelMap_sub_mulKernelMap (aug_comp_face εQ 0)
    (aug_comp_face εQ 1) φ.toRingHom φ'.toRingHom hφ hφ' χ.toRingHom hχ hχ₀' hχ₁' k).symm⟩

/-- **The canonical map `Coker_P → Coker_Q`** between the cokernels of `d₀ - d₁` of two
resolutions, induced by any map `P₀ → Q₀` over `B`. -/
def cokerMap : torTwoCoker hP ⟶ torTwoCoker hQ :=
  cokerMapOfLift hP hQ (exists_isLift hP hQ).choose (exists_isLift hP hQ).choose_spec

/-- The canonical map of cokernels is the map induced by any lift `P₀ → Q₀` over `B`. -/
theorem cokerMap_eq (φ : P.obj (op ⦋0⦌) →ₐ[A] Q.obj (op ⦋0⦌)) (hφ : IsLift (ε := ε) (εQ := εQ) φ) :
    cokerMap hP hQ = cokerMapOfLift hP hQ φ hφ :=
  cokerMapOfLift_eq hP hQ _ _ _ _

/-- The canonical maps of cokernels compose: the composite `Coker_P → Coker_Q → Coker_R` is the
canonical map `Coker_P → Coker_R`. -/
theorem cokerMap_comp : cokerMap hP hQ ≫ cokerMap hQ hR = cokerMap hP hR := by
  have : Fact (Function.Surjective (aug ε 0)) := ⟨aug_surjective hP 0⟩
  have : Fact (Function.Surjective (aug εQ 0)) := ⟨aug_surjective hQ 0⟩
  have : Fact (Function.Surjective (aug εR 0)) := ⟨aug_surjective hR 0⟩
  obtain ⟨φ, hφ⟩ := exists_isLift hP hQ
  obtain ⟨φ', hφ'⟩ := exists_isLift hQ hR
  have hc : IsLift (ε := ε) (εQ := εR) (φ'.comp φ) := by
    show (aug εR 0).comp (φ'.toRingHom.comp φ.toRingHom) = aug ε 0
    rw [← RingHom.comp_assoc, hφ', hφ]
  rw [cokerMap_eq hP hQ φ hφ, cokerMap_eq hQ hR φ' hφ', cokerMap_eq hP hR _ hc]
  refine torTwoCoker_hom_ext hP _ _ fun k => ?_
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact (mulKernelMap_comp φ.toRingHom hφ φ'.toRingHom hφ' k).symm

/-- The canonical map from the cokernel of a resolution to itself is the identity. -/
theorem cokerMap_self : cokerMap hP hP = 𝟙 _ := by
  have : Fact (Function.Surjective (aug ε 0)) := ⟨aug_surjective hP 0⟩
  have hid : IsLift (ε := ε) (εQ := ε) (AlgHom.id A _) := RingHom.comp_id _
  rw [cokerMap_eq hP hP _ hid]
  refine torTwoCoker_hom_ext hP _ _ fun k => ?_
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact mulKernelMap_id k

/-- **The cokernel of `d₀ - d₁ : Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B)` does not depend on the
resolution**: the canonical isomorphism between the cokernels for two resolutions of `B` over
`A`, induced by any map `P₀ → Q₀` over `B`. -/
def torTwoCokerIso : torTwoCoker hP ≅ torTwoCoker hQ where
  hom := cokerMap hP hQ
  inv := cokerMap hQ hP
  hom_inv_id := by rw [cokerMap_comp, cokerMap_self]
  inv_hom_id := by rw [cokerMap_comp, cokerMap_self]

end Transfer

end Stacks.Cotangent.TorTwo.Resolution

end
