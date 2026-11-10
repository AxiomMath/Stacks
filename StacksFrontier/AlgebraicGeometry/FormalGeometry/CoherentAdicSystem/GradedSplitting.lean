module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.Finsupp.Weight
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.RingTheory.ReesAlgebra.ExtendLinearMaps

/-!
# The graded splitting of a coherent adic system

Let `I = (f₁, …, f_r)` be an ideal of a Noetherian ring `A` with `cd(A, I) = 1`, let `c ≥ 1` and
let `φ_j : I ^ c ⟶ A` split the inclusion of `I ^ c` into `I` against the generators, as supplied
by [Stacks, Tag 0EIA]. Let `X` be a Noetherian scheme over `Spec A`, let `(F_n)` be a coherent
adic system along `I · 𝒪_X` and let `F = lim F_n`. [Stacks, Tag 0EH6] produces, after enlarging
`c`, a unique graded `𝒪_X`-module map

`Φ_F : ⨁_{n ≥ 0} I ^ (n c) F ⟶ F[T₁, …, T_r]`

characterized by `Φ_F (g s) = Φ(g) s` for `g ∈ I ^ (n c)` and `s` a local section of `F`, where
`Φ` is the graded algebra map of [Stacks, Tag 0EIB].

This file states that characterization — `Stacks.Coherent.IsGradedSplitting` — and proves that it
determines `Φ_F` completely.

## Main definitions

* `Stacks.Coherent.baseSectionHom` — the ring map `A ⟶ Γ(X, U)` induced by `X ⟶ Spec A`.
* `Stacks.Coherent.reesMonomial` — an element of `I ^ (n d)` as a degree-`n` element of the Rees
  algebra of `I ^ d`.
* `Stacks.Coherent.GradedSplittingComponents` — a graded map into `F[T₁, …, T_r]`, given by its
  component at each monomial.
* `Stacks.Coherent.IsGradedSplitting` — the local-section formula `Φ_F (g s) = Φ(g) s`.
* `Stacks.Coherent.pushSubmodule` — a submodule of a submodule of `F`, as a submodule of `F`.

## Main results

* `Stacks.Coherent.gradedSplitting_unique` — the local-section formula determines the graded map.
* `Stacks.Coherent.existsUnique_gradedSplitting_of_exists` — hence, once one such map exists, it
  is unique.
* `Stacks.Coherent.hom_ext_of_baseSmul` — the general statement behind both: two maps out of
  `I ^ k F` which agree on the products `g · m` with `g ∈ I ^ k ⊆ A` are equal.

## The unrestricted `@[stacks 0EH6]` is in `GradedSplittingCharts`

Only the uniqueness half of [Stacks, Tag 0EH6] is carried here, and the two tag attributes below
say so. The *existence* of `Φ_F` — with the enlargement of `c` it requires, and the identity that
`Φ_F` followed by `T_j ↦ f_j` is the inclusion `⨁ I ^ (n d) F ⟶ ⨁ I ^ n F` — is proved in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentAdicSystem/GradedSplittingCharts.lean`.
There
`Stacks.Coherent.exists_gradedSplitting` builds the map, and
`Stacks.Coherent.existsUnique_gradedSplitting` states the tag without restriction, combining that
existence with `gradedSplitting_unique` below.

The route taken there is the source's: reduce to an affine `X`, where [Stacks, Tag 087W] turns
`(F_n)` into a finite module `N` over the `I`-adic completion of `Γ(X, 𝒪_X)`, apply
[Stacks, Tag 0EIC] to `N` — available here as
`Stacks.ReesAlgebra.exists_unique_extendLinearMaps_module` — and glue the affine-local maps over
the charts of a finite affine cover, a single exponent `d` serving all of them.

## Implementation notes

The subsheaf `I ^ k F` is `Stacks.Algebraization.idealPowerMultiple`, the least subsheaf of `F`
containing `(I · 𝒪_X)(V) ^ k · Γ(F, V)` over every affine open `V`; this is the spelling the rest
of the coherent-adic-system material uses, and it does not need `F` to be quasi-coherent, which
matters because `F = lim F_n` is not.

Uniqueness is therefore *not* proved by computing the sections of `I ^ k F` over an affine open:
that computation (`Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine`) needs
quasi-coherence. Instead the locus where two maps `q, q' : I ^ k F ⟶ G` agree is turned into a
subsheaf of `F` — the pushforward `pushSubmodule` along the inclusion of the sectionwise kernel
of `q - q'` — and the affine-local universal property of `I ^ k F` is applied to that subsheaf.
This is why the hypothesis only has to mention products over affine opens.

A graded map is recorded by its component at each monomial `σ` of `T₁, …, T_r`, that component
being defined on the piece `I ^ (σ.degree · d) F`; the grading condition is then built into the
indexing instead of being a separate clause.

`AlgebraicGeometry.Scheme.Modules` is a `def`, so instance search does not unfold it to
`SheafOfModules X.ringCatSheaf` and the additive structure on morphisms is invisible at the
latter spelling. `asModules` names the sheaf of modules underlying a submodule at the
`X.Modules` spelling, which is what makes `q - q'` elaborate.

## References

* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 0EIA](https://stacks.math.columbia.edu/tag/0EIA)
* [Stacks Project, Tag 0EIB](https://stacks.math.columbia.edu/tag/0EIB)
* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.Algebraization Stacks.Cohomology.FormalFunctions Stacks.ReesAlgebra
open scoped AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules.Submodule (asModules)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Submodules of submodules -/

/-- A submodule of a submodule `P` of `F`, pushed forward to a submodule of `F`.

Over every open its sections are the image of those of `D`. This is a subsheaf: a section lying
locally in that image lies in `P` because `P` is a subsheaf, and the resulting section of `P`
lies in `D` because `D` is one. -/
public def pushSubmodule {X : Scheme.{u}} {F : X.Modules} (P : F.Submodule)
    (D : (asModules P).Submodule) : F.Submodule where
  toSubmodule :=
    { obj W := Submodule.map (P.toSubmodule.obj W).subtype (D.toSubmodule.obj W)
      map := by
        intro W W' k s hs
        obtain ⟨u, hu, rfl⟩ := hs
        exact ⟨(asModules P).val.map k u, D.toSubmodule.map_mem k hu, rfl⟩ }
  isSheaf := by
    intro W s hs
    have hP : s ∈ P.toSubmodule.obj W := by
      refine P.isSheaf s ((Opens.grothendieckTopology X).superset_covering ?_ hs)
      intro V f hf
      obtain ⟨u, _, hu2⟩ := hf
      change _ ∈ P.toSubmodule.toSubfunctor.obj (op V)
      exact hu2 ▸ u.2
    refine ⟨⟨s, hP⟩, ?_, rfl⟩
    refine D.isSheaf _ ((Opens.grothendieckTopology X).superset_covering ?_ hs)
    intro V f hf
    obtain ⟨u, hu1, hu2⟩ := hf
    change _ ∈ D.toSubmodule.toSubfunctor.obj (op V)
    have he : (asModules P).val.map f.op ⟨s, hP⟩ = u := Subtype.ext hu2.symm
    exact he ▸ hu1

/-- A section of `P` lies in `pushSubmodule P D` exactly when it lies in `D`. -/
public lemma mem_pushSubmodule {X : Scheme.{u}} {F : X.Modules} (P : F.Submodule)
    (D : (asModules P).Submodule) (W : (Opens X)ᵒᵖ) (s : F.val.obj W)
    (h : s ∈ P.toSubmodule.obj W) :
    s ∈ (pushSubmodule P D).toSubmodule.obj W ↔
      (⟨s, h⟩ : P.toSubmodule.obj W) ∈ D.toSubmodule.obj W := by
  constructor
  · rintro ⟨u, hu, hu2⟩
    exact (Subtype.ext hu2 : u = (⟨s, h⟩ : P.toSubmodule.obj W)) ▸ hu
  · intro hu
    exact ⟨⟨s, h⟩, hu, rfl⟩

/-- A product `r · m` with `r ∈ I(V) ^ k` is a section of `I ^ k M` over the affine open `V`. -/
public lemma mem_idealPowerMultiple_of_mem_smul {X : Scheme.{u}} (I : X.IdealSheafData) (k : ℕ)
    (M : X.Modules) (V : X.affineOpens) {s : Γ(M, V.1)}
    (hs : s ∈ I.ideal V ^ k • (⊤ : Submodule Γ(X, V) Γ(M, V))) :
    s ∈ (idealPowerMultiple I k M).toSubmodule.obj (op V.1) :=
  (idealPowerMultiple_le_iff I k M _).mp le_rfl V hs

/-- A section of `I ^ k F` lies in the pushforward of the sectionwise kernel of `q - q'` exactly
when `q` and `q'` agree on it. -/
private lemma mem_pushSubmodule_kernel_iff {X : Scheme.{u}} {F G : X.Modules} (P : F.Submodule)
    (q q' : asModules P ⟶ G) (W : X.Opens) (s : F.val.obj (op W))
    (hs : s ∈ P.toSubmodule.obj (op W)) :
    s ∈ (pushSubmodule P (kernelSubmodule (q - q'))).toSubmodule.obj (op W) ↔
      Scheme.Modules.Hom.app q W ⟨s, hs⟩ = Scheme.Modules.Hom.app q' W ⟨s, hs⟩ := by
  rw [mem_pushSubmodule _ _ _ s hs, kernelSubmodule_toSubmodule_obj, ← sub_eq_zero]
  rfl

/-- Two morphisms out of `P` are equal if `P` lies in the pushforward of the sectionwise kernel of
their difference. -/
private lemma hom_ext_of_le_pushSubmodule {X : Scheme.{u}} {F G : X.Modules} (P : F.Submodule)
    (q q' : asModules P ⟶ G) (key : P ≤ pushSubmodule P (kernelSubmodule (q - q'))) : q = q' :=
  Scheme.Modules.hom_ext q q' fun W => by
    ext t
    exact (mem_pushSubmodule_kernel_iff P q q' W t.1 t.2).1 (key (op W) t.2)

/-- Two morphisms out of `I ^ k F` agreeing on the products `r · m` over affine opens, with `r`
in `I(V) ^ k`, are equal.

The sections where the two agree are the sectionwise kernel of their difference, which
`pushSubmodule` presents as a subsheaf of `F`; the hypothesis says exactly that this subsheaf
satisfies the affine-local lower bound defining `I ^ k F`. -/
public lemma hom_ext_of_smul {X : Scheme.{u}} {F G : X.Modules} (I : X.IdealSheafData) (k : ℕ)
    (q q' : asModules (idealPowerMultiple I k F) ⟶ G)
    (h : ∀ (V : X.affineOpens) (s : Γ(F, V.1))
        (hs : s ∈ I.ideal V ^ k • (⊤ : Submodule Γ(X, V) Γ(F, V))),
        Scheme.Modules.Hom.app q V.1 ⟨s, mem_idealPowerMultiple_of_mem_smul I k F V hs⟩ =
          Scheme.Modules.Hom.app q' V.1 ⟨s, mem_idealPowerMultiple_of_mem_smul I k F V hs⟩) :
    q = q' :=
  hom_ext_of_le_pushSubmodule _ q q' <| (idealPowerMultiple_le_iff I k F _).2 fun V s hs =>
    (mem_pushSubmodule_kernel_iff _ q q' V.1 s _).2 (h V s hs)

/-! ### Sections and ideals coming from the base -/

/-- The ring map `A ⟶ Γ(X, U)` induced by a morphism `X ⟶ Spec A`. -/
public def baseSectionHom (A : Type u) [CommRing A] {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (U : X.Opens) : A →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top (a := U))).op).hom.comp
    ((Scheme.ΓSpecIso (.of A)).inv ≫ fX.appTop).hom

/-- Over an affine open, the ideal of `I · 𝒪_X` is the ideal generated by the image of `I`. -/
public lemma baseIdealSheaf_ideal_eq_map (A : Type u) [CommRing A] (J : Ideal A)
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (V : X.affineOpens) :
    (baseIdealSheaf A J fX).ideal V = Ideal.map (baseSectionHom A fX V.1) J := by
  rw [baseIdealSheaf_ideal, baseIdeal, Ideal.map_map]
  rfl

/-- Over an affine open, the `k`-th power of the ideal of `I · 𝒪_X` is generated by the image
of `I ^ k`. -/
public lemma baseIdealSheaf_ideal_pow_eq_map (A : Type u) [CommRing A] (J : Ideal A)
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (V : X.affineOpens) (k : ℕ) :
    (baseIdealSheaf A J fX).ideal V ^ k = Ideal.map (baseSectionHom A fX V.1) (J ^ k) := by
  rw [baseIdealSheaf_ideal_eq_map, Ideal.map_pow]

/-- Two morphisms out of `I ^ k F` agreeing on the products `g · m` with `g` in the image of
`I ^ k ⊆ A` are equal.

Over an affine open the ideal `(I · 𝒪_X)(V) ^ k` is generated by the image of `I ^ k`, so the
submodule it cuts out of `Γ(F, V)` is spanned by those products; `hom_ext_of_smul` then applies
after a span induction. -/
public lemma hom_ext_of_baseSmul (A : Type u) [CommRing A] (J : Ideal A) {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (k : ℕ) {F G : X.Modules}
    (q q' : asModules (idealPowerMultiple (baseIdealSheaf A J fX) k F) ⟶ G)
    (h : ∀ (V : X.affineOpens) (g : A) (_hg : g ∈ J ^ k) (m : Γ(F, V.1))
        (hmem : baseSectionHom A fX V.1 g • m ∈
          (idealPowerMultiple (baseIdealSheaf A J fX) k F).toSubmodule.obj (op V.1)),
        Scheme.Modules.Hom.app q V.1 ⟨baseSectionHom A fX V.1 g • m, hmem⟩ =
          Scheme.Modules.Hom.app q' V.1 ⟨baseSectionHom A fX V.1 g • m, hmem⟩) :
    q = q' := by
  classical
  refine hom_ext_of_le_pushSubmodule _ q q' <|
    (idealPowerMultiple_le_iff (baseIdealSheaf A J fX) k F _).2 fun W => ?_
  have hspan : ∀ r ∈ Ideal.map (baseSectionHom A fX W.1) (J ^ k), ∀ m : Γ(F, W.1),
      r • m ∈ (pushSubmodule (idealPowerMultiple (baseIdealSheaf A J fX) k F)
        (kernelSubmodule (q - q'))).toSubmodule.obj (op W.1) := by
    intro r hr
    refine Submodule.span_induction ?_ ?_ ?_ ?_
      (show r ∈ Ideal.span (baseSectionHom A fX W.1 '' (J ^ k : Ideal A)) from hr)
    · rintro x ⟨g, hg, rfl⟩ m
      have hrx : baseSectionHom A fX W.1 g ∈ (baseIdealSheaf A J fX).ideal W ^ k := by
        rw [baseIdealSheaf_ideal_pow_eq_map]
        exact Ideal.mem_map_of_mem _ hg
      have hmem : baseSectionHom A fX W.1 g • m ∈
          (idealPowerMultiple (baseIdealSheaf A J fX) k F).toSubmodule.obj (op W.1) :=
        mem_idealPowerMultiple_of_mem_smul _ k F W
          (Submodule.smul_mem_smul hrx Submodule.mem_top)
      exact (mem_pushSubmodule_kernel_iff _ q q' W.1 _ hmem).2 (h W g hg m hmem)
    · intro m
      rw [zero_smul]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy m
      rw [add_smul]
      exact Submodule.add_mem _ (hx m) (hy m)
    · intro a x _ hx m
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ a (hx m)
  rw [baseIdealSheaf_ideal_pow_eq_map]
  exact Submodule.smul_le.2 fun r hr m _ => hspan r hr m

/-! ### The graded splitting -/

/-- An element of `J ^ (n d)` as a homogeneous element of degree `n` of the Rees algebra of
`J ^ d`. -/
public def reesMonomial {A : Type u} [CommRing A] (J : Ideal A) (d n : ℕ)
    (g : (J ^ (n * d) : Ideal A)) : reesAlgebra (J ^ d) :=
  ⟨Polynomial.monomial n (g : A), reesAlgebra.monomial_mem.mpr
    (by simpa only [pow_mul, mul_comm] using g.property)⟩

/-- A graded `𝒪_X`-module map `⨁_{n ≥ 0} I ^ (n d) F ⟶ F[T₁, …, T_r]`, recorded by its component
at each monomial `σ`; that component is defined on the piece `I ^ (σ.degree · d) F`. -/
public abbrev GradedSplittingComponents (A : Type u) [CommRing A] (J : Ideal A)
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) (F : X.Modules) (r d : ℕ) :=
  ∀ σ : Fin r →₀ ℕ,
    asModules (idealPowerMultiple (baseIdealSheaf A J fX) (σ.degree * d) F) ⟶ F

/-- The characterizing property of the graded map of [Stacks, Tag 0EH6]: on a product `g · m`
with `g ∈ I ^ (n d)` and `m` a local section of `F`, the component at a monomial `σ` of degree
`n` takes the value `Φ(g)_σ · m`, where `Φ` is the graded algebra map `⨁ I ^ (n d) ⟶ A[T]` of
[Stacks, Tag 0EIB] attached to `ψ`. -/
public def IsGradedSplitting (A : Type u) [CommRing A] (J : Ideal A) {X : Scheme.{u}}
    (fX : X ⟶ Spec (.of A)) (F : X.Modules) {r : ℕ} (d : ℕ)
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (Ψ : GradedSplittingComponents A J fX F r d) : Prop :=
  ∀ (σ : Fin r →₀ ℕ) (U : X.Opens) (g : A) (hg : g ∈ J ^ (σ.degree * d)) (m : Γ(F, U))
    (hmem : baseSectionHom A fX U g • m ∈
      (idealPowerMultiple (baseIdealSheaf A J fX) (σ.degree * d) F).toSubmodule.obj (op U)),
    Scheme.Modules.Hom.app (Ψ σ) U ⟨baseSectionHom A fX U g • m, hmem⟩ =
      baseSectionHom A fX U
        ((extendLinearMaps (J ^ d) ψ (reesMonomial J d σ.degree ⟨g, hg⟩)).coeff σ) • m

/-- The uniqueness half of [Stacks, Tag 0EH6]. Let `I = (f₁, …, f_r)` be an ideal of a Noetherian
ring `A` with `cd(A, I) = 1`, let `φ_j : I ^ c ⟶ A` split the inclusion against the generators,
let `X` be a Noetherian scheme over `Spec A` and let `(F_n)` be a coherent adic system along
`I · 𝒪_X` with inverse limit `F`. Then the local-section formula `Φ_F (g s) = Φ(g) s` determines
the graded map `⨁_{n ≥ 0} I ^ (n d) F ⟶ F[T₁, …, T_r]` completely.

This is one half of the tag and so carries no `@[stacks]` attribute: 0EH6 asserts that such a
map exists *and* is unique, and this supplies only the uniqueness. It is consumed as a lemma by
`Stacks.Coherent.existsUnique_gradedSplitting` (`CoherentAdicSystem/GradedSplittingCharts.lean`),
which states the whole of 0EH6 — the enlargement of `c` to a `d`, the existence and uniqueness
of `Φ_F`, and the evaluation composite — under no hypothesis beyond the source's, and which is
where the tag is registered. -/
public theorem gradedSplitting_unique (A : Type u) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) {r : ℕ} (f : Fin r → A) (_hf : J = Ideal.span (Set.range f))
    (_hcd : Stacks.LocalCohomology.cohomologicalDimension A J (IsNoetherian.noetherian J) = 1)
    {c : ℕ} (_hc : 1 ≤ c) (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (_hφ : ∀ x : (J ^ c : Ideal A), (∑ j, f j * φ j x) = (x : A))
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) [AlgebraicGeometry.IsNoetherian X]
    (S : ℕᵒᵖ ⥤ X.Modules) (_hS : IsCoherentAdicSystem (baseIdealSheaf A J fX) S)
    {d : ℕ} (_hd : c ≤ d) (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (_hψ : ∀ x : (J ^ d : Ideal A), (∑ j, f j * ψ j x) = (x : A))
    (Ψ Ψ' : GradedSplittingComponents A J fX (limit S) r d)
    (hΨ : IsGradedSplitting A J fX (limit S) d ψ Ψ)
    (hΨ' : IsGradedSplitting A J fX (limit S) d ψ Ψ') :
    Ψ = Ψ' := by
  funext σ
  refine hom_ext_of_baseSmul A J fX (σ.degree * d) (Ψ σ) (Ψ' σ) fun V g hg m hmem => ?_
  rw [hΨ σ V.1 g hg m hmem, hΨ' σ V.1 g hg m hmem]

/-- Unique existence of the graded map of [Stacks, Tag 0EH6] from its existence: a graded map
satisfying the local-section formula `Φ_F (g s) = Φ(g) s` is unique as soon as there is one.

The hypothesis `hex` is the existence assertion of 0EH6 itself, so this statement is a step
towards the tag and not the tag, and carries no `@[stacks]` attribute. Existence is proved,
with no such hypothesis, in `Stacks.Coherent.existsUnique_gradedSplitting`
(`CoherentAdicSystem/GradedSplittingCharts.lean`), which states the whole of 0EH6 and is where
the tag is registered. -/
public theorem existsUnique_gradedSplitting_of_exists (A : Type u) [CommRing A]
    [IsNoetherianRing A]
    (J : Ideal A) {r : ℕ} (f : Fin r → A) (hf : J = Ideal.span (Set.range f))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A J (IsNoetherian.noetherian J) = 1)
    {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ x : (J ^ c : Ideal A), (∑ j, f j * φ j x) = (x : A))
    {X : Scheme.{u}} (fX : X ⟶ Spec (.of A)) [AlgebraicGeometry.IsNoetherian X]
    (S : ℕᵒᵖ ⥤ X.Modules) (hS : IsCoherentAdicSystem (baseIdealSheaf A J fX) S)
    {d : ℕ} (hd : c ≤ d) (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (hψ : ∀ x : (J ^ d : Ideal A), (∑ j, f j * ψ j x) = (x : A))
    (hex : ∃ Ψ : GradedSplittingComponents A J fX (limit S) r d,
      IsGradedSplitting A J fX (limit S) d ψ Ψ) :
    ∃! Ψ : GradedSplittingComponents A J fX (limit S) r d,
      IsGradedSplitting A J fX (limit S) d ψ Ψ := by
  obtain ⟨Ψ, hΨ⟩ := hex
  exact ⟨Ψ, hΨ, fun Ψ' hΨ' =>
    gradedSplitting_unique A J f hf hcd hc φ hφ fX S hS hd ψ hψ Ψ' Ψ hΨ' hΨ⟩

end Stacks.Coherent

end
