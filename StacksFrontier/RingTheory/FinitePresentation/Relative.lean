module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation

/-! # Modules finitely presented relative to a base ring

Let `R → A` be a map of commutative rings and let `M` be an `A`-module. Choosing a surjective
`R`-algebra map `α : R[x_1, …, x_n] → A` makes `M` a module over the polynomial ring
`R[x_1, …, x_n]` by restriction of scalars along `α`, and `M` is said to be *finitely presented
relative to `R`* when it is finitely presented over such a polynomial ring.

## Main definitions

* `Module.FinitePresentationRel`: `M` is finitely presented over `R[x_1, …, x_n]` for *some*
  surjective presentation `α : R[x_1, …, x_n] → A` (Stacks 05GZ).
* `Module.FinitePresentationRel.AllPresentations`: the same holds for *every* such presentation.
* `Module.FinitePresentationRel.AllFPCovers`: the same holds over every finitely presented
  `R`-algebra surjecting onto `A`.

## Main results

* `Module.FinitePresentationRel.finitePresentation`: a module finitely presented relative to `R`
  is a finitely presented `A`-module.
* `Module.finitePresentationRel_iff`: when `A` itself is a finitely presented `R`-algebra, being
  finitely presented relative to `R` is the same as being a finitely presented `A`-module.

In Lean the polynomial ring `R[x_1, …, x_n]` is `MvPolynomial (Fin n) R`, and restriction of
scalars of an `A`-module `M` along a ring map `f` is `Module.compHom M f`.
-/

@[expose] public section

universe u

/-- `M` is *finitely presented relative to `R`*: for some surjective `R`-algebra map
`α : R[x_1, …, x_n] → A`, the module `M` viewed over `R[x_1, …, x_n]` via `α` is finitely
presented. -/
@[stacks 05GZ]
def Module.FinitePresentationRel (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
    @Module.FinitePresentation (MvPolynomial (Fin n) R) M _ _ (Module.compHom M α.toRingHom)

/-- For *every* surjective `R`-algebra map `α : R[x_1, …, x_n] → A`, the module `M` viewed over
`R[x_1, …, x_n]` via `α` is finitely presented. This is condition (2) of Stacks 05GY. -/
def Module.FinitePresentationRel.AllPresentations (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    @Module.FinitePresentation (MvPolynomial (Fin n) R) M _ _ (Module.compHom M α.toRingHom)

/-- For every finitely presented `R`-algebra `A'` and every surjective `R`-algebra map
`π : A' → A`, the module `M` viewed over `A'` via `π` is finitely presented. This is condition (3)
of Stacks 05GY; the universe of the covering algebra `A'` is a free parameter. -/
def Module.FinitePresentationRel.AllFPCovers (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (A' : Type u) [CommRing A'] [Algebra R A'], Algebra.FinitePresentation R A' →
    ∀ (π : A' →ₐ[R] A), Function.Surjective π →
      @Module.FinitePresentation A' M _ _ (Module.compHom M π.toRingHom)

/-- If `S` and `T` act on `N` compatibly with a ring map `f : S → T`, then `N` is a scalar tower
over `S` and `T`, where `T` is an `S`-algebra via `f`. -/
private theorem isScalarTower_of_smul_eq {S T N : Type*} [CommRing S] [CommRing T]
    [AddCommGroup N] [Module S N] [Module T N] (f : S →+* T)
    (h : ∀ (s : S) (n : N), s • n = f s • n) :
    letI := f.toAlgebra
    IsScalarTower S T N :=
  letI := f.toAlgebra
  ⟨fun s t n => by
    rw [Algebra.smul_def, mul_smul]
    exact (h _ _).symm⟩

/-- Descent of finite presentation along a surjective ring map: if `f : S → T` is surjective and
the `T`-module `N`, viewed over `S` via `f`, is finitely presented, then `N` is finitely presented
over `T`. -/
theorem Module.finitePresentation_of_compHom {S T N : Type*} [CommRing S] [CommRing T]
    [AddCommGroup N] [Module T N] (f : S →+* T) (hf : Function.Surjective f)
    (h : @Module.FinitePresentation S N _ _ (Module.compHom N f)) :
    Module.FinitePresentation T N := by
  let _ : Algebra S T := f.toAlgebra
  let _ : Module S N := Module.compHom N f
  have : IsScalarTower S T N := isScalarTower_of_smul_eq f fun _ _ => rfl
  have : Module.FinitePresentation S N := h
  have : Module.Finite S T := Module.Finite.of_surjective (Algebra.linearMap S T) hf
  have : Module.Finite T N := Module.Finite.of_restrictScalars_finite S T N
  obtain ⟨t, g, hg⟩ := Module.Finite.exists_fin' T N
  have hker : (Submodule.restrictScalars S (LinearMap.ker g)).FG := by
    rw [← LinearMap.ker_restrictScalars S g]
    exact Module.FinitePresentation.fg_ker (g.restrictScalars S) hg
  exact (Module.FinitePresentation.fg_ker_iff g hg).mp (Submodule.FG.of_restrictScalars S hker)

/-- Ascent of finite presentation along a surjective ring map with finitely generated kernel: if
`f : S → T` is surjective with `RingHom.ker f` finitely generated and `N` is a finitely presented
`T`-module, then `N`, viewed over `S` via `f`, is finitely presented. -/
theorem Module.finitePresentation_compHom {S T N : Type*} [CommRing S] [CommRing T]
    [AddCommGroup N] [Module T N] (f : S →+* T) (hf : Function.Surjective f)
    (hfg : (RingHom.ker f).FG) [Module.FinitePresentation T N] :
    @Module.FinitePresentation S N _ _ (Module.compHom N f) := by
  let _ : Algebra S T := f.toAlgebra
  let _ : Module S N := Module.compHom N f
  have : IsScalarTower S T N := isScalarTower_of_smul_eq f fun _ _ => rfl
  have : Module.FinitePresentation S T := by
    exact Module.finitePresentation_of_surjective (Algebra.linearMap S T) hf hfg
  exact Module.FinitePresentation.trans S N T

/-- Ascent of finite presentation along a composite: if `p : S → T` is surjective with finitely
generated kernel and the `U`-module `N`, viewed over `T` via `g : T → U`, is finitely presented,
then `N` viewed over `S` via `g ∘ p` is finitely presented. -/
theorem Module.finitePresentation_compHom_comp {S T U N : Type*} [CommRing S] [CommRing T]
    [CommRing U] [AddCommGroup N] [Module U N] (g : T →+* U) (p : S →+* T)
    (hp : Function.Surjective p) (hfg : (RingHom.ker p).FG)
    (h : @Module.FinitePresentation T N _ _ (Module.compHom N g)) :
    @Module.FinitePresentation S N _ _ (Module.compHom N (g.comp p)) := by
  let _ : Algebra S T := p.toAlgebra
  let _ : Module T N := Module.compHom N g
  let _ : Module S N := Module.compHom N (g.comp p)
  have : IsScalarTower S T N := isScalarTower_of_smul_eq p fun _ _ => rfl
  have : Module.FinitePresentation T N := h
  have : Module.FinitePresentation S T := by
    exact Module.finitePresentation_of_surjective (Algebra.linearMap S T) hp hfg
  exact Module.FinitePresentation.trans S N T

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- A module finitely presented relative to `R` is a finitely presented `A`-module. -/
@[stacks 05GY "the final conclusion, that a module finitely presented relative to R is a finitely \
presented A-module"]
theorem Module.FinitePresentationRel.finitePresentation
    (h : Module.FinitePresentationRel R A M) : Module.FinitePresentation A M := by
  obtain ⟨n, α, hα, hfp⟩ := h
  exact Module.finitePresentation_of_compHom α.toRingHom hα hfp

/-- If `A` is a finitely presented `R`-algebra, then an `A`-module is finitely presented relative
to `R` exactly when it is a finitely presented `A`-module. -/
theorem Module.finitePresentationRel_iff [Algebra.FinitePresentation R A] :
    Module.FinitePresentationRel R A M ↔ Module.FinitePresentation A M := by
  refine ⟨Module.FinitePresentationRel.finitePresentation, fun h => ?_⟩
  obtain ⟨n, α, hαsurj, hαker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  exact ⟨n, α, hαsurj, Module.finitePresentation_compHom α.toRingHom hαsurj hαker⟩

/-- A presentation of `A` indexed by an arbitrary finite type suffices: if `α : R[σ] → A` is a
surjective `R`-algebra map with `σ` finite and `M` is finitely presented over `R[σ]` via `α`, then
`M` is finitely presented relative to `R`. -/
theorem Module.FinitePresentationRel.of_finite {σ : Type*} [Finite σ]
    (α : MvPolynomial σ R →ₐ[R] A) (hα : Function.Surjective α)
    (hfp : @Module.FinitePresentation (MvPolynomial σ R) M _ _
      (Module.compHom M α.toRingHom)) :
    Module.FinitePresentationRel R A M := by
  classical
  have := Fintype.ofFinite σ
  let φ : MvPolynomial σ R ≃ₐ[R] MvPolynomial (Fin (Fintype.card σ)) R :=
    MvPolynomial.renameEquiv R (Fintype.equivFin σ)
  refine ⟨Fintype.card σ, α.comp φ.symm.toAlgHom, hα.comp φ.symm.surjective, ?_⟩
  have hker : (RingHom.ker φ.symm.toAlgHom.toRingHom).FG := by
    rw [(RingHom.injective_iff_ker_eq_bot φ.symm.toAlgHom.toRingHom).mp φ.symm.injective]
    exact Submodule.fg_bot
  exact Module.finitePresentation_compHom_comp α.toRingHom φ.symm.toAlgHom.toRingHom
    φ.symm.surjective hker hfp
