module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Vanishing of Ext after flat base change of an injective module

Let `R` be a Noetherian ring, let `S` be a flat `R`-algebra, let `E` be an injective `R`-module
and let `N` be a finite `R`-module. The main result
`Module.subsingleton_ext_baseChange_of_injective` states that all the higher Ext-groups
`Ext^{q+1}_S(S ⊗[R] N, S ⊗[R] E)` vanish. In other words `S ⊗[R] E` behaves like an injective
`S`-module as far as base changes of finite `R`-modules are concerned.

## Proof idea

The underlying reason is the base change isomorphism
`Ext^i_S(S ⊗[R] N, S ⊗[R] E) ≅ S ⊗[R] Ext^i_R(N, E)`, but only its degree-zero incarnation is
needed, and that one is already available as
`Module.FinitePresentation.isBaseChange_map`. The argument is an induction on `q` during which
the module `N` varies.

Choose a surjection `p : (Fin m → R) →ₗ[R] N` and let `K = ker p`, a finite `R`-module because
`R` is Noetherian. Since `S` is flat over `R`, base change turns
`0 → K → (Fin m → R) → N → 0` into a short exact sequence of `S`-modules
`0 → S ⊗[R] K → S ⊗[R] (Fin m → R) → S ⊗[R] N → 0` whose middle term is a projective
`S`-module, because `S ⊗[R] (Fin m → R) ≅ (Fin m → S)`. All higher Ext out of the middle term
therefore vanish, and the contravariant long exact sequence of Ext exhibits
`Ext^{q+1}_S(S ⊗ N, S ⊗ E)` as a quotient of `Ext^q_S(S ⊗ K, S ⊗ E)`.

For `q ≥ 1` that group vanishes by the induction hypothesis applied to the finite module `K`.
For `q = 0` it does not vanish, but every `S`-linear map `S ⊗ K → S ⊗ E` extends to
`S ⊗ (Fin m → R)`: such a map is a sum of maps of the form `s • h.baseChange S` with
`h : K →ₗ[R] E`, which is what `Module.FinitePresentation.isBaseChange_map` provides, `K` being
finitely presented over the Noetherian ring `R`; each `h` extends along `K → (Fin m → R)` by
injectivity of `E`. Classes in `Ext^0` restricted from the middle term are killed by the
connecting map, so the quotient is trivial in this case too.

## Implementation notes

The induction is carried out in the private lemma `aux`, whose statement quantifies over `N`
*inside* the induction so that the inductive hypothesis can be applied to the kernel `K`.
The private lemmas `subsingleton_ext_succ` and `exists_comp_mk₀` isolate the purely homological
content and are stated for an arbitrary abelian category.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Module.subsingleton_ext_baseChange_of_injective

section Homological

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

/-- If the middle term of a short exact sequence `T` has vanishing `Ext^{q+1}` into `Y`, and if
every element of `Ext^q(T.X₁, Y)` is the restriction along `T.f` of an element of
`Ext^q(T.X₂, Y)`, then `Ext^{q+1}(T.X₃, Y)` vanishes. -/
private lemma subsingleton_ext_succ {T : ShortComplex C} (hT : T.ShortExact) (Y : C) (q : ℕ)
    [Subsingleton (Abelian.Ext T.X₂ Y (q + 1))]
    (hsurj : ∀ x₁ : Abelian.Ext T.X₁ Y q, ∃ x₂ : Abelian.Ext T.X₂ Y q,
      (Abelian.Ext.mk₀ T.f).comp x₂ (zero_add q) = x₁) :
    Subsingleton (Abelian.Ext T.X₃ Y (q + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x₃ ↦ ?_
  obtain ⟨x₁, rfl⟩ :=
    Abelian.Ext.contravariant_sequence_exact₃ hT Y x₃ (by subsingleton) (Nat.add_comm 1 q)
  obtain ⟨x₂, rfl⟩ := hsurj x₁
  simp

/-- Surjectivity of restriction along `T.f` on morphisms into `Y` gives the corresponding
surjectivity on `Ext^0`, through the identification `Ext^0(X, Y) ≃ (X ⟶ Y)`. -/
private lemma exists_comp_mk₀ {T : ShortComplex C} (Y : C)
    (h : ∀ u : T.X₁ ⟶ Y, ∃ v : T.X₂ ⟶ Y, T.f ≫ v = u) (x₁ : Abelian.Ext T.X₁ Y 0) :
    ∃ x₂ : Abelian.Ext T.X₂ Y 0, (Abelian.Ext.mk₀ T.f).comp x₂ (zero_add 0) = x₁ := by
  obtain ⟨v, hv⟩ := h (Abelian.Ext.homEquiv₀ x₁)
  exact ⟨Abelian.Ext.mk₀ v, by rw [Abelian.Ext.mk₀_comp_mk₀, hv, Abelian.Ext.mk₀_homEquiv₀_apply]⟩

end Homological

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

omit [Module.Flat R S] in
/-- The base change of a finite free `R`-module along `R → S` is a projective `S`-module, since
`S ⊗[R] (Fin m → R) ≅ (Fin m → S)`. -/
private lemma projective_baseChange_pi (m : ℕ) : Module.Projective S (S ⊗[R] (Fin m → R)) :=
  Module.Projective.of_equiv (TensorProduct.piScalarRight R S S (Fin m)).symm

variable (S) in
/-- The base change along `R → S` of the short exact sequence
`0 → ker p → (Fin m → R) → N → 0` attached to a surjection `p` from a finite free module,
viewed as a short complex of `S`-modules. -/
private noncomputable def kerShortComplex {N : Type u} [AddCommGroup N] [Module R N] {m : ℕ}
    (p : (Fin m → R) →ₗ[R] N) : ShortComplex (ModuleCat.{u} S) where
  X₁ := ModuleCat.of S (S ⊗[R] LinearMap.ker p)
  X₂ := ModuleCat.of S (S ⊗[R] (Fin m → R))
  X₃ := ModuleCat.of S (S ⊗[R] N)
  f := ModuleCat.ofHom ((LinearMap.ker p).subtype.baseChange S)
  g := ModuleCat.ofHom (p.baseChange S)
  zero := by ext x; simp [← LinearMap.baseChange_comp]

variable (S) in
/-- Flatness of `S` over `R` makes `kerShortComplex` short exact. -/
private lemma kerShortComplex_shortExact {N : Type u} [AddCommGroup N] [Module R N] {m : ℕ}
    (p : (Fin m → R) →ₗ[R] N) (hp : Function.Surjective p) :
    (kerShortComplex S p).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map p))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker p).injective_subtype)
    (LinearMap.lTensor_surjective S hp)

omit [Module.Flat R S] in
variable (S) in
/-- The middle term of `kerShortComplex` is a projective object. -/
private lemma projective_kerShortComplex_X₂ {N : Type u} [AddCommGroup N] [Module R N] {m : ℕ}
    (p : (Fin m → R) →ₗ[R] N) : CategoryTheory.Projective (kerShortComplex S p).X₂ :=
  have : Module.Projective S (S ⊗[R] (Fin m → R)) := projective_baseChange_pi m
  inferInstanceAs (CategoryTheory.Projective (ModuleCat.of S (S ⊗[R] (Fin m → R))))

/-- Let `E` be an injective `R`-module, let `K` be a finitely presented `R`-module and let
`ι : K →ₗ[R] A` be injective. Then every `S`-linear map `S ⊗[R] K →ₗ[S] S ⊗[R] E` factors
through the base change of `ι`.

Finite presentation of `K` together with flatness of `S` identifies `S ⊗[R] (K →ₗ[R] E)` with
`S ⊗[R] K →ₗ[S] S ⊗[R] E`; on a generator `s ⊗ₜ h` one extends `h` along `ι` using injectivity
of `E`. -/
private lemma exists_comp_baseChange (E : Type u) [AddCommGroup E] [Module R E]
    [Module.Injective R E] {K A : Type u} [AddCommGroup K] [Module R K] [AddCommGroup A]
    [Module R A] [Module.FinitePresentation R K] (ι : K →ₗ[R] A) (hι : Function.Injective ι)
    (ψ : (S ⊗[R] K) →ₗ[S] (S ⊗[R] E)) :
    ∃ φ : (S ⊗[R] A) →ₗ[S] (S ⊗[R] E), φ ∘ₗ ι.baseChange S = ψ := by
  have hbc : IsBaseChange S (LinearMap.baseChangeHom R S K E) :=
    Module.FinitePresentation.isBaseChange_map R K E S
  suffices H : ∀ t : S ⊗[R] (K →ₗ[R] E),
      ∃ φ : (S ⊗[R] A) →ₗ[S] (S ⊗[R] E), φ ∘ₗ ι.baseChange S = hbc.equiv t by
    obtain ⟨φ, hφ⟩ := H (hbc.equiv.symm ψ)
    exact ⟨φ, by simpa using hφ⟩
  intro t
  induction t with
  | tmul s h =>
      obtain ⟨h', hh'⟩ := Module.Injective.extension_property R E K A ι hι h
      refine ⟨s • h'.baseChange S, ?_⟩
      rw [hbc.equiv_tmul, LinearMap.smul_comp, ← LinearMap.baseChange_comp, hh']
      rfl
  | add x y hx hy =>
      obtain ⟨φx, hφx⟩ := hx
      obtain ⟨φy, hφy⟩ := hy
      exact ⟨φx + φy, by rw [LinearMap.add_comp, hφx, hφy, map_add]⟩

/-- To show `Ext^{q+1}_S(S ⊗[R] N, S ⊗[R] E) = 0` for a finite `R`-module `N`, it suffices to show
that, for a finite free presentation `p` of `N`, every `Ext^q` class on the base change of `ker p`
is a restriction from the base change of the free module. -/
private lemma subsingleton_ext_of_ker [IsNoetherianRing R] (E : Type u) [AddCommGroup E]
    [Module R E] (q : ℕ) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (H : ∀ {m : ℕ} (p : (Fin m → R) →ₗ[R] N) [Module.Finite R (LinearMap.ker p)],
      ∀ x₁ : Abelian.Ext (kerShortComplex S p).X₁ (ModuleCat.of S (S ⊗[R] E)) q,
        ∃ x₂ : Abelian.Ext (kerShortComplex S p).X₂ (ModuleCat.of S (S ⊗[R] E)) q,
          (Abelian.Ext.mk₀ (kerShortComplex S p).f).comp x₂ (zero_add q) = x₁) :
    Subsingleton
      (Abelian.Ext (ModuleCat.of S (S ⊗[R] N)) (ModuleCat.of S (S ⊗[R] E)) (q + 1)) := by
  obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin' R N
  have : Module.Finite R (LinearMap.ker p) := .of_fg (IsNoetherian.noetherian (LinearMap.ker p))
  have := projective_kerShortComplex_X₂ S p
  have : Subsingleton (Abelian.Ext (kerShortComplex S p).X₂ (ModuleCat.of S (S ⊗[R] E)) (q + 1)) :=
    Abelian.Ext.subsingleton_of_projective _ _ q
  exact subsingleton_ext_succ (kerShortComplex_shortExact S p hp) _ q (H p)

/-- For every finite `R`-module `N`, the group `Ext^{q+1}_S(S ⊗[R] N, S ⊗[R] E)` vanishes. The
module `N` is quantified inside the statement, so that an induction on `q` can be applied to the
kernel of a finite free presentation of `N`. -/
private lemma aux [IsNoetherianRing R] (E : Type u) [AddCommGroup E] [Module R E]
    [Module.Injective R E] (q : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      Subsingleton
        (Abelian.Ext (ModuleCat.of S (S ⊗[R] N)) (ModuleCat.of S (S ⊗[R] E)) (q + 1)) := by
  induction q with
  | zero =>
      intro N _ _ _
      refine subsingleton_ext_of_ker E 0 N fun p _ ↦ exists_comp_mk₀ _ fun u ↦ ?_
      have := Module.finitePresentation_of_finite R (LinearMap.ker p)
      obtain ⟨φ, hφ⟩ := exists_comp_baseChange E (LinearMap.ker p).subtype
        (LinearMap.ker p).injective_subtype u.hom
      exact ⟨ModuleCat.ofHom φ, ModuleCat.hom_ext hφ⟩
  | succ q ih =>
      intro N _ _ _
      refine subsingleton_ext_of_ker E (q + 1) N fun p _ _ ↦ ⟨0, ?_⟩
      have : Subsingleton
          (Abelian.Ext (kerShortComplex S p).X₁ (ModuleCat.of S (S ⊗[R] E)) (q + 1)) :=
        ih (LinearMap.ker p)
      subsingleton

end Module.subsingleton_ext_baseChange_of_injective

/-- Let `R` be a Noetherian ring, let `S` be a flat `R`-algebra, let `E` be an injective
`R`-module and let `N` be a finite `R`-module. Then all the higher Ext-groups
`Ext^{q+1}_S(S ⊗[R] N, S ⊗[R] E)` vanish: the flat base change of an injective module is
injective relative to the base changes of finite modules. -/
public theorem Module.subsingleton_ext_baseChange_of_injective
    {R S : Type u} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S]
    (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E]
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] (q : ℕ) :
    Subsingleton (Abelian.Ext (ModuleCat.of S (S ⊗[R] N)) (ModuleCat.of S (S ⊗[R] E)) (q + 1)) :=
  Module.subsingleton_ext_baseChange_of_injective.aux E q N

end
