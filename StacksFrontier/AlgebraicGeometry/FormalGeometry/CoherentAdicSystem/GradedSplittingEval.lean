module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplitting
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic
public import StacksFrontier.RingTheory.ReesAlgebra.ExtendEval

/-!
# The composite of the graded splitting with `T_j ↦ f_j` is the inclusion

Let `I = (f₁, …, f_r)` be an ideal of a commutative ring `A`, let `X` be a scheme over
`Spec A`, let `F` be an `𝒪_X`-module and let

`Φ_F : ⨁_{n ≥ 0} I ^ (n d) F ⟶ F[T₁, …, T_r]`

be a graded map satisfying the local-section formula `Φ_F (g s) = Φ(g) s` of
[Stacks, Tag 0EH6] — in this repository a `Stacks.Coherent.GradedSplittingComponents` satisfying
`Stacks.Coherent.IsGradedSplitting`. The last clause of [Stacks, Tag 0EH6] says that composing
`Φ_F` with the substitution `T_j ↦ f_j` returns the canonical inclusion
`⨁_n I ^ (n d) F ⟶ ⨁_n I ^ n F`.

This file proves that clause. It is not an extra condition on `Φ_F`: it follows from the
local-section formula alone, because on a product `g · m` the clause is the algebraic identity
`∑_{|σ| = n} f^σ · Φ(g)_σ = g` of `Stacks.ReesAlgebra.sum_pow_mul_extendCoeff` multiplied by
`m`, and a map out of `I ^ (n d) F` is determined by its values on those products
(`Stacks.Coherent.hom_ext_of_baseSmul`).

## Main definitions

* `Stacks.Coherent.gradedSplittingComponentAt` — the component of a graded splitting at a
  monomial `σ` of degree `n`, read as a map out of `I ^ (n d) F` rather than out of
  `I ^ (σ.degree · d) F`.
* `Stacks.Coherent.gradedSplittingEvalHom` — the substitution `T_j ↦ f_j` applied to `Φ_F` in
  degree `n`: the weighted sum `∑_{|σ| = n} f^σ · Ψ_σ`, as a morphism of `𝒪_X`-modules
  `I ^ (n d) F ⟶ F`.

## Main results

* `Stacks.Coherent.gradedSplittingEvalHom_app` — the morphism acts on sections by that weighted
  sum.
* `Stacks.Coherent.gradedSplittingEvalHom_eq_ι` — **the clause**: that morphism is the
  inclusion `I ^ (n d) F ⟶ F`.
* `Stacks.Coherent.sum_pow_smul_gradedSplitting` — the same, read on a section.
* `Stacks.Coherent.baseSectionHom_map`, `Stacks.Coherent.app_presheaf_map` and
  `Stacks.Coherent.presheaf_map_smul` — the three compatibilities with restriction the gluing
  asks for, each stated in the `AlgebraicGeometry.Scheme.Modules.presheaf` spelling so that one
  `rw` chain closes the naturality of the weighted sum.

## Implementation notes

A component `Ψ σ` of a graded splitting is a map out of `I ^ (σ.degree · d) F`, while the
degree-`n` part of the substitution is a map out of `I ^ (n d) F`. For a monomial `σ` of degree
`n` the two exponents are equal but not syntactically so. Rather than transport sections — the
membership proof mentions the exponent, and the scalar action on the sections of a submodule
sheaf is registered at a different spelling of the scalar ring, so an ascribed
`c • ⟨s, h⟩` does not elaborate — the transport is done once, on the *subsheaf*, by
`SheafOfModules.Submodule.homOfLE` at the equality of the two exponents. Every linearity and
naturality statement below is then the corresponding statement for a single morphism of
`𝒪_X`-modules, with no subtype built by hand.

The weighted sum has to be a morphism of `𝒪_X`-modules, not merely a family of maps on
sections, because `Stacks.Coherent.hom_ext_of_baseSmul` compares morphisms. Nothing in this
repository multiplies a morphism of sheaves of modules by a global section, so the morphism is
produced from its action on sections by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover` at the one-element cover
`{⊤}`, the local data being packaged as a `TopCat.Sheaf.LocalModuleHom` on `⊤`.

## References

* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 0EIB](https://stacks.math.columbia.edu/tag/0EIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.Algebraization Stacks.Cohomology.FormalFunctions Stacks.ReesAlgebra
open scoped AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules.Submodule (asModules ιModules)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Two transports -/

/-- A section of `I ^ k M` is a section of `I ^ l M` for an exponent `l` equal to `k`. The two
are the same subsheaf, but the exponent appears in the statement of the membership. -/
public lemma mem_idealPowerMultiple_of_exponent_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    {k l : ℕ} (h : k = l) (M : X.Modules) {W : X.Opens} {s : Γ(M, W)}
    (hs : s ∈ (idealPowerMultiple I l M).toSubmodule.obj (op W)) :
    s ∈ (idealPowerMultiple I k M).toSubmodule.obj (op W) := by
  subst h
  exact hs

/-- The ring map `A ⟶ Γ(X, U)` of `Stacks.Coherent.baseSectionHom` is compatible with
restriction. -/
public lemma baseSectionHom_map (A : Type u) [CommRing A] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) {U V : X.Opens} (h : V ≤ U) (a : A) :
    (X.presheaf.map (homOfLE h).op).hom (baseSectionHom A fX U a) =
      baseSectionHom A fX V a := by
  have hmap : X.presheaf.map (homOfLE (le_top (a := U))).op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (le_top (a := V))).op := by
    rw [← X.presheaf.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hmap
    (((Scheme.ΓSpecIso (.of A)).inv ≫ fX.appTop).hom a)

/-- The action on sections of a morphism of `𝒪_X`-modules commutes with restriction, in the
`Scheme.Modules.presheaf` spelling the gluing of morphisms uses. -/
public lemma app_presheaf_map {X : Scheme.{u}} {M N : X.Modules} (Q : M ⟶ N) {V W : X.Opens}
    (hWV : W ≤ V) (t : Γ(M, V)) :
    Scheme.Modules.Hom.app Q W (M.presheaf.map (homOfLE hWV).op t) =
      N.presheaf.map (homOfLE hWV).op (Scheme.Modules.Hom.app Q V t) :=
  NatTrans.naturality_apply Q.mapPresheaf (homOfLE hWV).op t

/-- Restriction of sections of an `𝒪_X`-module is semilinear along the restriction of scalars,
in the `Scheme.Modules.presheaf` spelling. -/
public lemma presheaf_map_smul {X : Scheme.{u}} (M : X.Modules) {V W : X.Opens} (hWV : W ≤ V)
    (c : Γ(X, V)) (x : Γ(M, V)) :
    M.presheaf.map (homOfLE hWV).op (c • x) =
      (X.presheaf.map (homOfLE hWV).op).hom c • M.presheaf.map (homOfLE hWV).op x :=
  M.val.map_smul (homOfLE hWV).op c x

/-! ### A component read at the degree of its monomial -/

variable {A : Type u} [CommRing A] {J : Ideal A} {X : Scheme.{u}} {fX : X ⟶ Spec (.of A)}
  {F : X.Modules} {r : ℕ} {d : ℕ}

/-- The component of a graded splitting at a monomial `σ` of degree `n`, read as a map out of
`I ^ (n d) F`. The two subsheaves `I ^ (σ.degree · d) F` and `I ^ (n d) F` are equal, and this
composes `Ψ σ` with the inclusion that equality provides. -/
public def gradedSplittingComponentAt (Ψ : GradedSplittingComponents A J fX F r d)
    {n : ℕ} {σ : Fin r →₀ ℕ} (hσ : Finsupp.degree σ = n) :
    asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F) ⟶ F :=
  _root_.SheafOfModules.Submodule.homOfLE
      (le_of_eq (congrArg
        (fun k => idealPowerMultiple (baseIdealSheaf A J fX) (k * d) F) hσ.symm)) ≫ Ψ σ

/-- `Stacks.Coherent.gradedSplittingComponentAt` acts on sections as the component it is built
from. -/
public lemma gradedSplittingComponentAt_app (Ψ : GradedSplittingComponents A J fX F r d)
    {n : ℕ} {σ : Fin r →₀ ℕ} (hσ : Finsupp.degree σ = n) (U : X.Opens) (s : Γ(F, U))
    (hs : s ∈ (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F).toSubmodule.obj (op U)) :
    Scheme.Modules.Hom.app (gradedSplittingComponentAt Ψ hσ) U ⟨s, hs⟩ =
      Scheme.Modules.Hom.app (Ψ σ) U
        ⟨s, mem_idealPowerMultiple_of_exponent_eq _ (congrArg (· * d) hσ) F hs⟩ :=
  rfl

/-! ### The substitution `T_j ↦ f_j`, on sections -/

/-- The degree-`n` part of the substitution `T_j ↦ f_j` applied to a graded splitting, on the
sections over a single open: `t ↦ ∑_{|σ| = n} f^σ · Ψ_σ(t)`. -/
public def gradedSplittingEval (Ψ : GradedSplittingComponents A J fX F r d) (f : Fin r → A)
    (n : ℕ) (V : X.Opens)
    (t : Γ(asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F), V)) : Γ(F, V) :=
  ∑ σ ∈ (degreeMonomials r n).attach,
    baseSectionHom A fX V (∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j) •
      Scheme.Modules.Hom.app
        (gradedSplittingComponentAt Ψ (mem_degreeMonomials.1 σ.2)) V t

/-- `Stacks.Coherent.gradedSplittingEval` is the weighted sum it is defined to be. -/
public lemma gradedSplittingEval_eq (Ψ : GradedSplittingComponents A J fX F r d)
    (f : Fin r → A) (n : ℕ) (V : X.Opens)
    (t : Γ(asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F), V)) :
    gradedSplittingEval Ψ f n V t =
      ∑ σ ∈ (degreeMonomials r n).attach,
        baseSectionHom A fX V (∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j) •
          Scheme.Modules.Hom.app
            (gradedSplittingComponentAt Ψ (mem_degreeMonomials.1 σ.2)) V t :=
  rfl

/-- The substitution is additive on sections. -/
public lemma gradedSplittingEval_add (Ψ : GradedSplittingComponents A J fX F r d)
    (f : Fin r → A) (n : ℕ) (V : X.Opens)
    (t u : Γ(asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F), V)) :
    gradedSplittingEval Ψ f n V (t + u) =
      gradedSplittingEval Ψ f n V t + gradedSplittingEval Ψ f n V u := by
  simp only [gradedSplittingEval, map_add, smul_add, Finset.sum_add_distrib]

/-- The substitution is `Γ(X, V)`-linear on sections. -/
public lemma gradedSplittingEval_smul (Ψ : GradedSplittingComponents A J fX F r d)
    (f : Fin r → A) (n : ℕ) (V : X.Opens) (c : Γ(X, V))
    (t : Γ(asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F), V)) :
    gradedSplittingEval Ψ f n V (c • t) = c • gradedSplittingEval Ψ f n V t := by
  simp only [gradedSplittingEval, Scheme.Modules.Hom.app_smul, Finset.smul_sum, smul_comm c]

/-- The substitution commutes with restriction. -/
public lemma gradedSplittingEval_map (Ψ : GradedSplittingComponents A J fX F r d)
    (f : Fin r → A) (n : ℕ) (V W : X.Opens) (hWV : W ≤ V)
    (t : Γ(asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F), V)) :
    gradedSplittingEval Ψ f n W
        ((asModules (idealPowerMultiple (baseIdealSheaf A J fX)
          (n * d) F)).presheaf.map (homOfLE hWV).op t) =
      F.presheaf.map (homOfLE hWV).op (gradedSplittingEval Ψ f n V t) := by
  rw [gradedSplittingEval, gradedSplittingEval, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [app_presheaf_map, presheaf_map_smul, baseSectionHom_map]

/-- The substitution as local morphism data on the whole of `X`, which is the shape the gluing
of morphisms of sheaves of modules consumes. -/
public def gradedSplittingEvalLocal (Ψ : GradedSplittingComponents A J fX F r d)
    (f : Fin r → A) (n : ℕ) :
    TopCat.Sheaf.LocalModuleHom
      (asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F)).val F.val ⊤ where
  app V _ := ModuleCat.ofHom
    { toFun := gradedSplittingEval Ψ f n V
      map_add' := gradedSplittingEval_add Ψ f n V
      map_smul' := gradedSplittingEval_smul Ψ f n V }
  naturality _ hWV s := gradedSplittingEval_map Ψ f n _ _ hWV s

/-- The degree-`n` part of the substitution `T_j ↦ f_j`, as a morphism of `𝒪_X`-modules. -/
public def gradedSplittingEvalHom (Ψ : GradedSplittingComponents A J fX F r d)
    (f : Fin r → A) (n : ℕ) :
    asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F) ⟶ F :=
  (Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover
    (M := asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F)) (N := F)
    (ι := PUnit.{u + 1}) (U := fun _ => (⊤ : X.Opens)) (by simp)
    (fun _ => gradedSplittingEvalLocal Ψ f n) (fun _ _ _ _ _ => rfl)).choose

/-- `Stacks.Coherent.gradedSplittingEvalHom` acts on sections by the weighted sum. -/
public lemma gradedSplittingEvalHom_app (Ψ : GradedSplittingComponents A J fX F r d)
    (f : Fin r → A) (n : ℕ) (V : X.Opens)
    (t : Γ(asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F), V)) :
    Scheme.Modules.Hom.app (gradedSplittingEvalHom Ψ f n) V t =
      gradedSplittingEval Ψ f n V t :=
  congr($((Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover
    (M := asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F)) (N := F)
    (ι := PUnit.{u + 1}) (U := fun _ => (⊤ : X.Opens)) (by simp)
    (fun _ => gradedSplittingEvalLocal Ψ f n)
    (fun _ _ _ _ _ => rfl)).choose_spec.1 PUnit.unit V le_top) t)

/-! ### The clause -/

/-- The value of a component of a graded splitting on a product, written with
`Stacks.ReesAlgebra.extendCoeff` at the degree of the monomial. -/
public lemma gradedSplittingComponentAt_app_smul {ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A}
    {Ψ : GradedSplittingComponents A J fX F r d} (hΨ : IsGradedSplitting A J fX F d ψ Ψ)
    {n : ℕ} {σ : Fin r →₀ ℕ} (hσ : Finsupp.degree σ = n) (U : X.Opens) (g : A)
    (hg : g ∈ J ^ (n * d)) (m : Γ(F, U))
    (hmem : baseSectionHom A fX U g • m ∈
      (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F).toSubmodule.obj (op U)) :
    Scheme.Modules.Hom.app (gradedSplittingComponentAt Ψ hσ) U
        ⟨baseSectionHom A fX U g • m, hmem⟩ =
      baseSectionHom A fX U
          (extendCoeff J d n ψ σ ⟨g, mem_pow_pow_of_mem_pow_mul J d n hg⟩) • m := by
  have hgσ : g ∈ J ^ (Finsupp.degree σ * d) := by rw [hσ]; exact hg
  have hσg := mem_pow_pow_of_mem_pow_mul J d (Finsupp.degree σ) hgσ
  rw [gradedSplittingComponentAt_app Ψ hσ U _ hmem,
    hΨ σ U g hgσ m (mem_idealPowerMultiple_of_exponent_eq _ (congrArg (· * d) hσ) F hmem)]
  refine congrArg (fun a => baseSectionHom A fX U a • m) ?_
  refine Eq.trans ?_ (extendCoeff_congr_degree J d ψ hσ σ g hσg
    (mem_pow_pow_of_mem_pow_mul J d n hg))
  exact (extendCoeff_apply J d (Finsupp.degree σ) ψ σ g hσg
    (reesMonomial J d (Finsupp.degree σ) ⟨g, hgσ⟩).2).symm

/-- **Stacks Project, Tag 0EH6**, the last clause. A graded map satisfying the local-section
formula `Φ_F (g s) = Φ(g) s`, composed with the substitution `T_j ↦ f_j`, is the canonical
inclusion `I ^ (n d) F ⟶ F` in every degree `n`.

Both sides are morphisms out of `I ^ (n d) F`, so by `Stacks.Coherent.hom_ext_of_baseSmul` it is
enough to compare them on a product `g · m` with `g ∈ I ^ (n d)`; there the left-hand side is
`(∑_{|σ| = n} f^σ · Φ(g)_σ) · m`, which is `g · m` by
`Stacks.ReesAlgebra.sum_pow_mul_extendCoeff`.

The graded map satisfying the local-section formula is a hypothesis: its existence is not proved
here, so Tag 0EH6 is not registered on this theorem. -/
public theorem gradedSplittingEvalHom_eq_ι (f : Fin r → A) (hf : ∀ j, f j ∈ J)
    {ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A}
    (hψ : ∀ x : (J ^ d : Ideal A), (∑ j, f j * ψ j x) = (x : A))
    {Ψ : GradedSplittingComponents A J fX F r d} (hΨ : IsGradedSplitting A J fX F d ψ Ψ)
    (n : ℕ) :
    gradedSplittingEvalHom Ψ f n =
      ιModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F) := by
  refine hom_ext_of_baseSmul A J fX (n * d) _ _ fun V g hg m hmem => ?_
  refine (gradedSplittingEvalHom_app Ψ f n V.1
    ⟨baseSectionHom A fX V.1 g • m, hmem⟩).trans ?_
  refine (gradedSplittingEval_eq Ψ f n V.1
    ⟨baseSectionHom A fX V.1 g • m, hmem⟩).trans ?_
  have hg' := mem_pow_pow_of_mem_pow_mul J d n hg
  have hterm : ∀ σ ∈ (degreeMonomials r n).attach,
      baseSectionHom A fX V.1 (∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j) •
          Scheme.Modules.Hom.app
            (gradedSplittingComponentAt Ψ (mem_degreeMonomials.1 σ.2)) V.1
            ⟨baseSectionHom A fX V.1 g • m, hmem⟩ =
        baseSectionHom A fX V.1
          ((∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j) *
            extendCoeff J d n ψ σ.1 ⟨g, hg'⟩) • m := by
    intro σ _
    rw [gradedSplittingComponentAt_app_smul hΨ (mem_degreeMonomials.1 σ.2) V.1 g hg m hmem,
      map_mul, mul_smul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ← map_sum,
    Finset.sum_attach (degreeMonomials r n)
      (fun σ => (∏ j, f j ^ σ j) * extendCoeff J d n ψ σ ⟨g, hg'⟩),
    sum_pow_mul_extendCoeff J d n f hf ψ hψ g hg']
  rfl

/-- **Stacks Project, Tag 0EH6**, the last clause, read on a section: for a section `t` of
`I ^ (n d) F` the weighted sum `∑_{|σ| = n} f^σ · Ψ_σ(t)` is `t` itself. -/
public theorem sum_pow_smul_gradedSplitting (f : Fin r → A) (hf : ∀ j, f j ∈ J)
    {ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A}
    (hψ : ∀ x : (J ^ d : Ideal A), (∑ j, f j * ψ j x) = (x : A))
    {Ψ : GradedSplittingComponents A J fX F r d} (hΨ : IsGradedSplitting A J fX F d ψ Ψ)
    (n : ℕ) (U : X.Opens)
    (t : Γ(asModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) F), U)) :
    (∑ σ ∈ (degreeMonomials r n).attach,
      baseSectionHom A fX U (∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j) •
        Scheme.Modules.Hom.app
          (gradedSplittingComponentAt Ψ (mem_degreeMonomials.1 σ.2)) U t) = t.1 := by
  have h := congrArg (fun q => Scheme.Modules.Hom.app q U t)
    (gradedSplittingEvalHom_eq_ι f hf hψ hΨ n)
  rw [gradedSplittingEvalHom_app] at h
  exact h

end Stacks.Coherent

end
