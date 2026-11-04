module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules and the Picard group of a ring

Let `R` be a commutative ring. An `R`-module `M` is *invertible* when tensoring with it is an
equivalence of the category of `R`-modules, and *trivial* when it is isomorphic to `R` itself.
Invertibility has two other descriptions: `M` is finite projective of rank one at every prime,
and `M` admits a tensor inverse. Any tensor inverse is then the linear dual of `M`, so the
invertible modules form a group under tensor product — the Picard group `CommRing.Pic R` — and
that group is trivial as soon as `R` is a domain with a normalizable gcd, in particular for a
unique factorization domain.

## Main definitions

* `Module.IsInvertibleModule`: invertibility of a module, phrased as the tensoring functor
  being an equivalence.
* `Module.IsTrivialInvertibleModule`: triviality of an invertible module, phrased as an
  isomorphism with the base ring.

## Main results

* `Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse`: the three
  descriptions of an invertible module agree, and every tensor inverse is the linear dual.
* `Module.isInvertibleModule_iff_invertible`: the functor description of invertibility, which
  is the one taken as the definition, agrees with `Module.Invertible`.

## Implementation notes

Finite locally free modules are represented as finite projective modules, and constant rank one
is expressed by `Module.rankAtStalk` being identically one. Isomorphism of modules is a nonempty
type of linear equivalences, so that the statements stay in `Prop`.

## References

* [Stacks Project, Tag 0B8H](https://stacks.math.columbia.edu/tag/0B8H)
* [Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
* [Stacks Project, Tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

/-! ### Invertible and trivial modules -/

section

universe u

@[expose] public section

open CategoryTheory

/-- An `R`-module `M` is invertible when the functor `M ⊗[R] -` is an equivalence of the
category of `R`-modules. -/
@[stacks 0B8H]
public abbrev Module.IsInvertibleModule
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)).IsEquivalence

/-- An invertible `R`-module is trivial if it is isomorphic to `R` as an `R`-module. -/
@[stacks 0B8H]
public abbrev Module.IsTrivialInvertibleModule
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  Nonempty (M ≃ₗ[R] R)

end

end

/-! ### Three descriptions of an invertible module -/

section

universe u v w

open TensorProduct

/-- For a finite projective `R`-module `M` and a submonoid `S` of `R`, the base change map
`Module.Dual.baseChange` from `Module.Dual R M` to the dual of `Localization S ⊗[R] M` is a
localization at `S`. -/
public theorem dual_baseChange_isLocalized {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] (S : Submonoid R) :
    IsLocalizedModule S (Module.Dual.baseChange (Localization S) (V := M)) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let A := Localization S
  let jM : M →ₗ[R] A ⊗[R] M := TensorProduct.mk R A M 1
  let jR : R →ₗ[R] A := Algebra.linearMap R A
  have h : IsLocalizedModule S (IsLocalizedModule.mapExtendScalars S jM jR A) := inferInstance
  convert h using 1
  ext f m
  show f m • (1 : A) = ((IsLocalizedModule.map S jM jR) f) (jM m)
  rw [IsLocalizedModule.map_apply]
  exact (Algebra.algebraMap_eq_smul_one (f m)).symm

/-- If `M` is finite projective of rank one at every prime, then its localization
`Localization.AtPrime P ⊗[R] M` at a maximal ideal `P` is an invertible module. -/
public theorem local_invertible_of_rankAtStalk_one {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M]
    (h : Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1)
    (P : Ideal R) [P.IsMaximal] :
    Module.Invertible (Localization.AtPrime P)
      (Localization.AtPrime P ⊗[R] M) := by
  let A := Localization.AtPrime P
  have : Module.Flat R M := inferInstance
  have : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank A (A ⊗[R] M) = 1 := by
    simpa [A] using
      (Module.rankAtStalk_eq_finrank_tensorProduct (M := M) ⟨P, inferInstance⟩).symm.trans
        (congrFun h ⟨P, inferInstance⟩)
  let e : A ≃ₗ[A] A ⊗[R] M := (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
  exact Module.Invertible.congr e

/-- For `M` finite projective of rank one at every prime and a maximal ideal `P`, the
localization at `P` of `Module.Dual R M ⊗[R] M` is isomorphic to `Localization.AtPrime P`,
via evaluation of functionals (see `local_eval_equiv_tmul`). -/
public noncomputable def local_eval_equiv {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (h : Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1)
    (P : Ideal R) [P.IsMaximal] :
    Localization.AtPrime P ⊗[R] (Module.Dual R M ⊗[R] M) ≃ₗ[Localization.AtPrime P]
      Localization.AtPrime P := by
  let S := P.primeCompl
  let A := Localization.AtPrime P
  have : IsLocalizedModule S (Module.Dual.baseChange A (V := M)) :=
    dual_baseChange_isLocalized S
  let eD : A ⊗[R] Module.Dual R M ≃ₗ[A] Module.Dual A (A ⊗[R] M) :=
    (IsLocalizedModule.isBaseChange S A (Module.Dual.baseChange A (V := M))).equiv
  letI : Module.Invertible A (A ⊗[R] M) := local_invertible_of_rankAtStalk_one h P
  exact AlgebraTensorModule.distribBaseChange R A (Module.Dual R M) M ≪≫ₗ
    TensorProduct.congr eD (.refl A (A ⊗[R] M)) ≪≫ₗ
    Module.Invertible.linearEquiv A (A ⊗[R] M)

/-- `local_eval_equiv` sends `a ⊗ (f ⊗ m)` to `a * f m`. -/
public theorem local_eval_equiv_tmul {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (h : Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1)
    (P : Ideal R) [P.IsMaximal]
    (a : Localization.AtPrime P) (f : Module.Dual R M) (m : M) :
    local_eval_equiv h P (a ⊗ₜ[R] (f ⊗ₜ[R] m)) =
      a * algebraMap R (Localization.AtPrime P) (f m) := by
  simp [local_eval_equiv, Module.Invertible.linearEquiv,
    Module.Dual.baseChange_apply_tmul, contractLeft_apply,
    IsBaseChange.equiv_tmul, Algebra.smul_def, mul_comm]

/-- A finite projective `R`-module of rank one at every prime is invertible. -/
public theorem invertible_of_finite_projective_rankAtStalk_one {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M]
    (h : Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1) :
    Module.Invertible R M := by
  constructor
  apply bijective_of_isLocalized_maximal
    (fun P _ => Localization.AtPrime P ⊗[R] (Module.Dual R M ⊗[R] M))
    (fun P _ => TensorProduct.mk R (Localization.AtPrime P) (Module.Dual R M ⊗[R] M) 1)
    (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap R (Localization.AtPrime P))
    (contractLeft R M)
  intro P hP
  let S := P.primeCompl
  let A := Localization.AtPrime P
  let jT : (Module.Dual R M ⊗[R] M) →ₗ[R] A ⊗[R] (Module.Dual R M ⊗[R] M) :=
    TensorProduct.mk R A _ 1
  let jR : R →ₗ[R] A := Algebra.linearMap R A
  let e := local_eval_equiv h P
  have heq : IsLocalizedModule.map S jT jR (contractLeft R M) =
      e.toLinearMap.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S jT jR
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f m =>
      simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply]
      simpa [jT, jR, e, contractLeft_apply] using
        (local_eval_equiv_tmul h P (1 : A) f m).symm
    | add x y hx hy =>
      simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply] at hx hy ⊢
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [heq]
  exact e.bijective

/-- Contraction on the right: for an invertible module, `M ⊗[R] Mᵛ ≃ₗ[R] R`. -/
private noncomputable def selfDualEquiv (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Invertible R M] : M ⊗[R] Module.Dual R M ≃ₗ[R] R :=
  TensorProduct.comm R M (Module.Dual R M) ≪≫ₗ Module.Invertible.linearEquiv R M

/-- **Stacks 0B8I.** For an `R`-module `M`, the following are equivalent: `M` is finite
projective of rank one at every prime, `M` is invertible, and `M` admits a tensor inverse.
Moreover, every tensor inverse of `M` is isomorphic to the linear dual of `M`. -/
@[stacks 0B8I]
public theorem Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    List.TFAE [
      Module.Finite R M ∧ Module.Projective R M ∧
        Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1,
      Module.Invertible R M,
      ∃ (N : Type (max u v)) (_ : AddCommGroup N) (_ : Module R N),
        Nonempty (TensorProduct R M N ≃ₗ[R] R)] ∧
      ∀ (N : Type w) [AddCommGroup N] [Module R N],
        Nonempty (TensorProduct R M N ≃ₗ[R] R) →
          Nonempty (N ≃ₗ[R] Module.Dual R M)
    := by
  let A : Prop := Module.Finite R M ∧ Module.Projective R M ∧
    Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1
  let B : Prop := Module.Invertible R M
  let C : Prop := ∃ (N : Type (max u v)) (_ : AddCommGroup N) (_ : Module R N),
    Nonempty (TensorProduct R M N ≃ₗ[R] R)
  have hAB : A ↔ B := by
    constructor
    · rintro ⟨hfin, hproj, hrank⟩
      have : Module.Finite R M := hfin
      have : Module.Projective R M := hproj
      exact invertible_of_finite_projective_rankAtStalk_one hrank
    · intro hinv
      have : Module.Invertible R M := hinv
      refine ⟨inferInstance, inferInstance, ?_⟩
      funext p
      let A := Localization.AtPrime p.asIdeal
      let S := p.asIdeal.primeCompl
      have : Module.Invertible A (LocalizedModule S M) := inferInstance
      have : Module.Free A (LocalizedModule S M) := Module.free_of_flat_of_isLocalRing
      exact Module.Invertible.finrank_eq_one A (LocalizedModule S M)
  have hBC : B ↔ C := by
    constructor
    · intro hinv
      have : Module.Invertible R M := hinv
      exact ⟨Module.Dual R M, inferInstance, inferInstance,
        ⟨selfDualEquiv R M⟩⟩
    · rintro ⟨N, hN, hNM, ⟨e⟩⟩
      let _ : AddCommGroup N := hN
      let _ : Module R N := hNM
      exact Module.Invertible.left e
  constructor
  · apply List.tfae_of_forall (b := B)
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hAB
    · exact Iff.rfl
    · exact hBC.symm
  · intro N _ _ ⟨e⟩
    exact ⟨Module.Invertible.linearEquivDual
      (TensorProduct.comm R N M ≪≫ₗ e)⟩

end

/-! ### Invertibility as an equivalence of the module category -/

section

universe u

@[expose] public section

open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- Tensoring linear maps on the left by an invertible module is a bijection on homs. -/
private theorem lTensor_bijective [Module.Invertible R M]
    {Y Z : Type u} [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] :
    Function.Bijective (fun f : Y →ₗ[R] Z => f.lTensor M) := by
  have h : (fun f : Y →ₗ[R] Z => f.lTensor M) =
      (LinearEquiv.arrowCongr (TensorProduct.comm R Y M) (TensorProduct.comm R Z M)) ∘
        (fun f : Y →ₗ[R] Z => f.rTensor M) := by
    funext f
    apply TensorProduct.ext'
    intro m y
    simp [LinearEquiv.arrowCongr]
  rw [h]
  exact (LinearEquiv.arrowCongr (TensorProduct.comm R Y M)
      (TensorProduct.comm R Z M)).bijective.comp
    (Module.Invertible.rTensorEquiv Y Z (selfDualEquiv R M)).bijective

/-- **Stacks 0B8I**, the description of invertibility the Stacks Project takes as its
definition in Tag 0B8H: `M ⊗[R] -` is an equivalence of the category of `R`-modules exactly
when `M` is invertible. Without this, `Module.IsInvertibleModule` and `Module.Invertible`
are two unrelated predicates and the equivalence above is about the wrong condition (2). -/
@[stacks 0B8I]
public theorem Module.isInvertibleModule_iff_invertible :
    Module.IsInvertibleModule R M ↔ Module.Invertible R M := by
  constructor
  · intro h
    have := h
    set F := (MonoidalCategory.tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)
    have iso : F.obj (F.inv.obj (ModuleCat.of R R)) ≅ ModuleCat.of R R :=
      F.asEquivalence.counitIso.app (ModuleCat.of R R)
    exact Module.Invertible.left
      (N := (F.inv.obj (ModuleCat.of R R) : ModuleCat.{u} R)) iso.toLinearEquiv
  · intro h
    have := h
    have hb {Y Z : ModuleCat.{u} R} := lTensor_bijective R M (Y := Y) (Z := Z)
    exact
      { faithful := ⟨fun {Y Z} f g hfg => by
          apply ModuleCat.hom_ext
          exact hb.1 (congrArg ModuleCat.Hom.hom hfg)⟩
        full := ⟨fun {Y Z} g => by
          obtain ⟨f, hf⟩ := hb.2 g.hom
          exact ⟨ModuleCat.ofHom f, by apply ModuleCat.hom_ext; exact hf⟩⟩
        essSurj := ⟨fun Z => ⟨ModuleCat.of R (Module.Dual R M ⊗[R] Z),
          ⟨(Module.Invertible.leftCancelEquiv (Z : Type u)
            (selfDualEquiv R M)).toModuleIso⟩⟩⟩ }

end

end

/-! ### The Picard group of a unique factorization domain -/

section

-- The former `@[stacks 0BCH]` declarations are now Mathlib's
-- `instSubsingletonPicOfIsDomainOfIsGCDMonoid`: the Picard group of a domain with a gcd is
-- trivial. A unique factorization domain is such a domain, so instance resolution closes the
-- Stacks statement directly. No `add_to_stacks` is needed here — Mathlib already carries
-- `@[stacks 0BCH]` on that instance itself (`Mathlib/RingTheory/PicardGroup.lean`), and a
-- second registration of the same pair is reported as a duplicate and skipped.

end
