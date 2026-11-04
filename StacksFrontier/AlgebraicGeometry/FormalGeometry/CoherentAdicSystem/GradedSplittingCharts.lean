module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplittingAffine
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplittingLimitSections

/-!
# The graded splitting of a coherent adic system

Let `I = (f₁, …, f_r)` be an ideal of a Noetherian ring `A` of cohomological dimension one, let
`φ_j : I ^ c ⟶ A` split the inclusion against the generators, let `X` be a Noetherian scheme
over `Spec A` and let `(F_n)` be a coherent adic system along `I · 𝒪_X` with inverse limit `F`.
This file completes [Stacks, Tag 0EH6]: after one enlargement of `c` to a `d`, with an adjusted
splitting `ψ`, there is a unique graded `𝒪_X`-module map

`Φ_F : ⨁_{n ≥ 0} I ^ (n d) F ⟶ F[T₁, …, T_r]`

satisfying the local-section formula `Φ_F (g s) = Φ(g) s`, and composing it with the
substitution `T_j ↦ f_j` gives back the inclusion `I ^ (n d) F ⟶ F`.

The construction of `Φ_F` from the single hypothesis that `ψ` kills the relations of `Γ(F, W)`
for the charts `W` of one affine cover is
`Stacks.Coherent.exists_gradedSplitting_of_killsRelationsHom_charts`. What is proved here is
that hypothesis, and it is proved by producing the exponent *once*, for the whole finite family
of charts at the same time:

* over an affine chart `W` the system restricts to a coherent adic system on `W` itself
  (`Stacks.Coherent.restrictSystem`), so [Stacks, Tag 087W] presents the inverse limit of its
  global sections as a finite module over the completion of `Γ(W, 𝒪_W)` and [Stacks, Tag 0EIC]
  applies — `Stacks.Coherent.exists_killsRelationsHom_globalSections_of_idealSheafData`;
* that inverse limit of global sections *is* the inverse limit of the sections over `W`, by
  `Stacks.Coherent.affineOpenLimitSemilinearEquiv`, and the two actions of `A` correspond across
  the open immersion by `Stacks.Coherent.topIso_hom_baseSectionHom`;
* a Noetherian scheme has a *finite* affine cover
  (`Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top`), so the
  enlargements supplied by its charts can be composed one after another, each keeping what the
  earlier ones proved by `Stacks.ReesAlgebra.KillsRelationsHom.of_restrictsSplitting`.

## Main results

* `Stacks.Coherent.topIso_inv_baseSectionHom` and `Stacks.Coherent.topIso_hom_baseSectionHom` —
  the ring map `A ⟶ Γ(X, U)` and the ring map `A ⟶ Γ(U, 𝒪_U)` of the open subscheme correspond
  under `AlgebraicGeometry.Scheme.Opens.topIso`.
* `Stacks.Coherent.killsRelationsHom_of_semilinearEquiv` — relation-killing transports along a
  semilinear equivalence whose ring isomorphism matches the two actions of the base.
* `Stacks.Coherent.exists_killsRelationsHom_globalSections_of_idealSheafData` — the affine
  application of [Stacks, Tag 0EIC], for an arbitrary quasi-coherent ideal sheaf.
* `Stacks.Coherent.killsRelationsHom_sectionsLimit_of_restrictSystem` — relation-killing for the
  inverse limit of global sections of the restricted system is relation-killing for the inverse
  limit of sections over the chart.
* `Stacks.Coherent.exists_killsRelationsHom_sectionsLimit` — hence one exponent for one chart,
  and `Stacks.Coherent.exists_killsRelationsHom_sectionsLimit_finset` — one exponent for a
  finite family of charts.
* `Stacks.Coherent.exists_gradedSplitting` — the existence of `Φ_F`, unconditionally.
* `Stacks.Coherent.existsUnique_gradedSplitting` — **[Stacks, Tag 0EH6]**: the enlargement of
  `c`, the adjusted splitting, and the existence and uniqueness of the graded map, which
  composed with `T_j ↦ f_j` is the ideal-power inclusion.

## References

* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Algebraization Stacks.Cohomology.FormalFunctions Stacks.ReesAlgebra
open scoped AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules.Submodule (asModules ιModules)

universe u

namespace Stacks.Coherent

attribute [local instance] ringHomInvPairOfRingEquiv ringHomInvPairOfRingEquivSymm

variable {X : Scheme.{u}}

/-! ### The action of the base across an open immersion -/

/-- **The ring map `A ⟶ Γ(X, U)` becomes the ring map `A ⟶ Γ(U, 𝒪_U)` of the open subscheme.**
Both are the restriction of the global function `A ⟶ Γ(X, 𝒪_X)` along the unique inclusion
`U.ι ''ᵁ ⊤ ≤ ⊤`, read through `AlgebraicGeometry.Scheme.Opens.topIso`. -/
public lemma topIso_inv_baseSectionHom (A : Type u) [CommRing A] (fX : X ⟶ Spec (.of A))
    (U : X.Opens) (a : A) :
    U.topIso.inv.hom (baseSectionHom A fX U a) = baseSectionHom A (U.ι ≫ fX) ⊤ a := by
  have hi : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have key : X.presheaf.map (homOfLE (le_top (a := U))).op ≫ U.topIso.inv =
      U.ι.appLE ⊤ ⊤ le_top := by
    rw [← hi, Scheme.Hom.map_appLE]
  exact ConcreteCategory.congr_hom key (((Scheme.ΓSpecIso (.of A)).inv ≫ fX.appTop).hom a)

/-- `Stacks.Coherent.topIso_inv_baseSectionHom` read in the other direction. -/
public lemma topIso_hom_baseSectionHom (A : Type u) [CommRing A] (fX : X ⟶ Spec (.of A))
    (U : X.Opens) (a : A) :
    U.topIso.hom.hom (baseSectionHom A (U.ι ≫ fX) ⊤ a) = baseSectionHom A fX U a := by
  rw [← topIso_inv_baseSectionHom A fX U a]
  exact ConcreteCategory.congr_hom U.topIso.inv_hom_id _

/-- **Relation-killing transports along a semilinear equivalence** whose ring isomorphism
matches the two actions of the base. This is the semilinear form of
`Stacks.ReesAlgebra.killsRelationsHom_of_injective`: the two modules live over different rings,
and the identification of those rings is what carries one action of `A` to the other. -/
public lemma killsRelationsHom_of_semilinearEquiv {A : Type u} [CommRing A]
    {R S : Type u} [CommRing R] [CommRing S] (σ : R ≃+* S) (fR : A →+* R) (fS : A →+* S)
    (hσ : ∀ a : A, σ.toRingHom (fR a) = fS a)
    {M : Type u} [AddCommGroup M] [Module R M] {N : Type u} [AddCommGroup N] [Module S N]
    (e : M ≃ₛₗ[σ.toRingHom] N) {J : Ideal A} {r d : ℕ}
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A) (h : KillsRelationsHom fR M J d ψ) :
    KillsRelationsHom fS N J d ψ := by
  have hπ : ∀ (a : A) (y : N), e.symm (fS a • y) = fR a • e.symm y := by
    intro a y
    refine e.injective ?_
    rw [LinearEquiv.apply_symm_apply, map_smulₛₗ, LinearEquiv.apply_symm_apply, hσ]
  exact killsRelationsHom_of_injective fS fR e.symm.toAddEquiv.toAddMonoidHom hπ
    e.symm.injective h

/-! ### One exponent for one affine chart -/

/-- **The affine application of [Stacks, Tag 0EIC] inside [Stacks, Tag 0EH6]**, for an arbitrary
quasi-coherent ideal sheaf. On an affine scheme every quasi-coherent ideal sheaf is
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop` of its ideal of global functions, by
`AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`, which is the shape
`Stacks.Coherent.exists_killsRelationsHom_globalSections` is stated for; the restriction of
`I · 𝒪_X` to an affine chart is of that shape without being written that way. -/
public theorem exists_killsRelationsHom_globalSections_of_idealSheafData
    (A : Type u) [CommRing A] (J : Ideal A) {r : ℕ} (gen : Fin r → A)
    (hgen : J = Ideal.span (Set.range gen)) (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ x : (J ^ c : Ideal A), (∑ j, gen j * φ j x) = (x : A))
    {Y : Scheme.{u}} [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] (fY : Y ⟶ Spec (.of A))
    (I : Y.IdealSheafData) (G : CoherentAdicSystems I) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting J hcd φ ψ ∧
      (∀ x : (J ^ d : Ideal A), (∑ j, gen j * ψ j x) = (x : A)) ∧
      KillsRelationsHom (baseSectionHom A fY ⊤)
        (limit (globalSectionsSystem G) : ModuleCat.{u} Γ(Y, ⊤)) J d ψ := by
  obtain ⟨K, rfl⟩ := Scheme.IdealSheafData.equivOfIsAffine.symm.surjective I
  exact exists_killsRelationsHom_globalSections A J gen hgen c hc φ hφ fY K G

/-- **Relation-killing passes from the restricted system to the chart.**

The inverse limit of the global sections of the restriction of `(F_n)` to an affine open `W` is
the inverse limit of the sections of `(F_n)` over `W`, by
`Stacks.Coherent.affineOpenLimitSemilinearEquiv`; the comparison is semilinear along the
identification `Γ(W, 𝒪_W) ≅ Γ(X, W)` of `AlgebraicGeometry.Scheme.Opens.topIso`, under which
the two actions of `A` correspond by `Stacks.Coherent.topIso_hom_baseSectionHom`. So
`Stacks.Coherent.killsRelationsHom_of_semilinearEquiv` transports the statement. -/
public theorem killsRelationsHom_sectionsLimit_of_restrictSystem (A : Type u) [CommRing A]
    (J : Ideal A) [IsNoetherian X] (fX : X ⟶ Spec (.of A)) (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) {r d : ℕ}
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (h : KillsRelationsHom (baseSectionHom A (U.1.ι ≫ fX) ⊤)
      (limit (globalSectionsSystem (restrictSystem I F U.1)) :
        ModuleCat.{u} Γ(U.1.toScheme, ⊤)) J d ψ) :
    KillsRelationsHom (baseSectionHom A fX U.1)
      (sectionsLimit F U.1 : ModuleCat.{u} Γ(X, U.1)) J d ψ :=
  killsRelationsHom_of_semilinearEquiv U.1.topIso.commRingCatIsoToRingEquiv
    (baseSectionHom A (U.1.ι ≫ fX) ⊤) (baseSectionHom A fX U.1)
    (topIso_hom_baseSectionHom A fX U.1) (affineOpenLimitSemilinearEquiv I F U) ψ h

/-- **One exponent for one affine chart.** The system restricts to a coherent adic system on the
chart, where [Stacks, Tag 0EIC] applies to the finite module over the completion that
[Stacks, Tag 087W] supplies; the resulting statement is then read on the sections over the chart
by `Stacks.Coherent.killsRelationsHom_sectionsLimit_of_restrictSystem`. -/
public theorem exists_killsRelationsHom_sectionsLimit (A : Type u) [CommRing A] (J : Ideal A)
    {r : ℕ} (gen : Fin r → A) (hgen : J = Ideal.span (Set.range gen)) (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ x : (J ^ c : Ideal A), (∑ j, gen j * φ j x) = (x : A))
    [IsNoetherian X] (fX : X ⟶ Spec (.of A)) (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (U : X.affineOpens) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting J hcd φ ψ ∧
      (∀ x : (J ^ d : Ideal A), (∑ j, gen j * ψ j x) = (x : A)) ∧
      KillsRelationsHom (baseSectionHom A fX U.1)
        (sectionsLimit F U.1 : ModuleCat.{u} Γ(X, U.1)) J d ψ := by
  have : IsAffine U.1.toScheme := U.2
  have : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨d, hcd, ψ, hres, hsplit, hkill⟩ :=
    exists_killsRelationsHom_globalSections_of_idealSheafData A J gen hgen c hc φ hφ
      (U.1.ι ≫ fX) (I.comap U.1.ι) (restrictSystem I F U.1)
  exact ⟨d, hcd, ψ, hres, hsplit,
    killsRelationsHom_sectionsLimit_of_restrictSystem A J fX I F U ψ hkill⟩

/-! ### One exponent for the charts of a finite affine cover -/

/-- **One exponent for finitely many affine charts at once.** Each chart enlarges the exponent
once, and `Stacks.ReesAlgebra.KillsRelationsHom.of_restrictsSplitting` keeps what the earlier
charts proved; so a `Finset` of affine opens is handled by a single enlargement. -/
public theorem exists_killsRelationsHom_sectionsLimit_finset (A : Type u) [CommRing A]
    (J : Ideal A) {r : ℕ} (gen : Fin r → A) (hgen : J = Ideal.span (Set.range gen)) (c : ℕ)
    (hc : 1 ≤ c) (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ x : (J ^ c : Ideal A), (∑ j, gen j * φ j x) = (x : A))
    [IsNoetherian X] (fX : X ⟶ Spec (.of A)) (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (s : Finset X.affineOpens) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting J hcd φ ψ ∧
      (∀ x : (J ^ d : Ideal A), (∑ j, gen j * ψ j x) = (x : A)) ∧
      ∀ U ∈ s, KillsRelationsHom (baseSectionHom A fX U.1)
        (sectionsLimit F U.1 : ModuleCat.{u} Γ(X, U.1)) J d ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, φ, fun _ _ _ => rfl, hφ, by simp⟩
  | insert V t _hV ih =>
      obtain ⟨d, hcd, ψ, hres, hsplit, hkill⟩ := ih
      obtain ⟨e, hde, χ, hres', hsplit', hkill'⟩ :=
        exists_killsRelationsHom_sectionsLimit A J gen hgen d (hc.trans hcd) ψ hsplit fX I F V
      refine ⟨e, hcd.trans hde, χ, hres.trans hres', hsplit', fun U hU => ?_⟩
      rcases Finset.mem_insert.1 hU with rfl | hUt
      · exact hkill'
      · exact (hkill U hUt).of_restrictsSplitting hres'

/-! ### The graded map -/

/-- **The existence half of [Stacks, Tag 0EH6], unconditionally.** A Noetherian scheme is
covered by finitely many affine opens, each of which supplies one enlargement of the exponent
by `Stacks.Coherent.exists_killsRelationsHom_sectionsLimit`; a single enlargement serving all of
them is what `Stacks.Coherent.exists_gradedSplitting_of_killsRelationsHom_charts` needs to build
the graded map. -/
public theorem exists_gradedSplitting (A : Type u) [CommRing A] (J : Ideal A) {r : ℕ}
    (gen : Fin r → A) (hgen : J = Ideal.span (Set.range gen)) (c : ℕ) (hc : 1 ≤ c)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ x : (J ^ c : Ideal A), (∑ j, gen j * φ j x) = (x : A))
    [IsNoetherian X] (fX : X ⟶ Spec (.of A))
    (F : CoherentAdicSystems (baseIdealSheaf A J fX)) :
    ∃ d : ℕ, ∃ hcd : c ≤ d, ∃ ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting J hcd φ ψ ∧
      (∀ x : (J ^ d : Ideal A), (∑ j, gen j * ψ j x) = (x : A)) ∧
      ∃ Ψ : GradedSplittingComponents A J fX (limit (C := X.Modules) F.obj) r d,
        IsGradedSplitting A J fX (limit (C := X.Modules) F.obj) d ψ Ψ := by
  obtain ⟨s, hs⟩ :=
    _root_.Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top
      (X := X)
  obtain ⟨d, hcd, ψ, hres, hsplit, hkill⟩ :=
    exists_killsRelationsHom_sectionsLimit_finset A J gen hgen c hc φ hφ fX
      (baseIdealSheaf A J fX) F s
  have hcov : (⨆ V : { V : X.affineOpens // V ∈ s }, (V.1.1 : X.Opens)) = ⊤ := by
    rw [iSup_subtype]
    exact hs
  exact ⟨d, hcd, ψ, hres, hsplit,
    exists_gradedSplitting_of_killsRelationsHom_charts A J fX F ψ
      (fun V : { V : X.affineOpens // V ∈ s } => V.1) hcov fun V => hkill V.1 V.2⟩

/-- **Stacks Project, Tag 0EH6.** Let `I = (f₁, …, f_r)` be an ideal of a Noetherian ring `A`
with `cd(A, I) = 1`, let `φ_j : I ^ c ⟶ A` split the inclusion against the generators, let `X`
be a Noetherian scheme over `Spec A` and let `(F_n)` be a coherent adic system along `I · 𝒪_X`
with inverse limit `F`. Then `c` may be enlarged to a `d`, with a splitting `ψ_j : I ^ d ⟶ A`
restricting `φ` and still splitting the inclusion, so that there is a *unique* graded
`𝒪_X`-module map

`Φ_F : ⨁_{n ≥ 0} I ^ (n d) F ⟶ F[T₁, …, T_r]`

with `Φ_F (g s) = Φ(g) s` for `g ∈ I ^ (n d)` and `s` a local section of `F`, and the composite
of `Φ_F` with the substitution `T_j ↦ f_j` is the inclusion `I ^ (n d) F ⟶ F` in every
degree. -/
@[stacks 0EH6]
public theorem existsUnique_gradedSplitting (A : Type u) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) {r : ℕ} (f : Fin r → A) (hf : J = Ideal.span (Set.range f))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A J (IsNoetherian.noetherian J) = 1)
    {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ x : (J ^ c : Ideal A), (∑ j, f j * φ j x) = (x : A))
    (fX : X ⟶ Spec (.of A)) [AlgebraicGeometry.IsNoetherian X]
    (S : ℕᵒᵖ ⥤ X.Modules) (hS : IsCoherentAdicSystem (baseIdealSheaf A J fX) S) :
    ∃ d : ℕ, ∃ hcd' : c ≤ d, ∃ ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A,
      RestrictsSplitting J hcd' φ ψ ∧
      (∀ x : (J ^ d : Ideal A), (∑ j, f j * ψ j x) = (x : A)) ∧
      ∃! Ψ : GradedSplittingComponents A J fX (limit S) r d,
        IsGradedSplitting A J fX (limit S) d ψ Ψ ∧
          ∀ n : ℕ, gradedSplittingEvalHom Ψ f n =
            ιModules (idealPowerMultiple (baseIdealSheaf A J fX) (n * d) (limit S)) := by
  have hfJ : ∀ j, f j ∈ J := fun j => hf ▸ Ideal.subset_span ⟨j, rfl⟩
  obtain ⟨d, hcd', ψ, hres, hsplit, Ψ, hΨ⟩ :=
    exists_gradedSplitting A J f hf c hc φ hφ fX ⟨S, hS⟩
  refine ⟨d, hcd', ψ, hres, hsplit, Ψ, ⟨hΨ, fun n =>
    gradedSplittingEvalHom_eq_ι f hfJ hsplit hΨ n⟩, fun Ψ' hΨ' => ?_⟩
  exact gradedSplitting_unique A J f hf hcd hc φ hφ fX S hS hcd' ψ hsplit Ψ' Ψ hΨ'.1 hΨ

end Stacks.Coherent

end
