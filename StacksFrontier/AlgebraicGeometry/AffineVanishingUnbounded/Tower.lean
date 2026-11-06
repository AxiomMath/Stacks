module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.AlgebraicGeometry.AffineVanishingBoundedBelow

/-!
# Unbounded affine vanishing from the derived limit of the truncations

Let `R` be a commutative ring and `M^\bullet` a cochain complex of `R`-modules, and write
`E = Q(\widetilde{M}^\bullet)` for the object of `D(\mathcal{O}_{\operatorname{Spec} R})`
represented by its degreewise sheafification. The last input of the derived Spec–Γ equivalence
(Stacks 06Z0) is that the comparison
`AlgebraicGeometry.globalSectionsComplexComparison`
$$ Q(\Gamma(\operatorname{Spec} R, \widetilde{M}^\bullet)) \longrightarrow R\Gamma(E) $$
is invertible for *every* `M^\bullet`, which is the affine case of Stacks 08D4.

This file runs the `E = R\lim \tau_{\geq -n}E` argument of that tag over an affine base, granted
its geometric input: that `E` *is* the derived limit of the tower of its truncations. More
precisely the input is taken in the shape Stacks 070F and 070M deliver it — a tower `𝓘` of
bounded below complexes with `Γ`-acyclic terms, maps `g_n` resolving the sheafified truncations
`\widetilde{(\tau_{\geq -n}M)}^\bullet`, and a distinguished triangle exhibiting `E` as the
derived limit of `𝓘` through the canonical cone — and the conclusion is the affine vanishing.

Everything after that input happens on the algebra side, in `D(R)`, and that is the point: the
`ℕ`-indexed products of `R`-modules are exact, so `D(R)` has the countable products and the
Mittag-Leffler argument of Stacks 090Y available, while the countable products of
`\mathcal{O}_X`-modules are *not* exact (a product of local surjections need not be locally
surjective), so the same argument is not available in `D(\mathcal{O}_X)`.

The three steps are these.

1. **Interchange.** `R\Gamma` carries the derived-limit triangle of `𝓘` to a derived-limit
   triangle in `D(R)`, by Stacks 08U1 — `Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`
   in the pinned form, whose structural map is the image of the given cone, so that its
   projections are `R\Gamma` of the canonical maps `E ⟶ Q(𝓘_n)`.
2. **The tower is eventually constant.** Each `𝓘_n` is bounded below with `Γ`-acyclic terms, so
   Leray's acyclicity lemma identifies `R\Gamma(Q(𝓘_n))` with `Q(\Gamma(𝓘_n))`; that complex is
   strictly `≥ -n`, which kills `H^r` for `r < -n`, and in degrees `r ≥ -n` the cone map is an
   isomorphism on `H^r` because `Γ(g_n)` is a quasi-isomorphism (Leray again, the terms of
   `\widetilde{(\tau_{\geq -n}M)}^\bullet` being quasi-coherent) and
   `Γ(\widetilde{\pi}) = \pi_{\tau_{\geq -n}}` is one in those degrees (`Γ ∘ {}^\sim` is the
   identity).
3. **Conclusion.** `CochainComplex.isIso_of_isDerivedLimit_of_eventually_isIso_homologyMap`, the
   content of Stacks 090Y, applied to that triangle and that cone, says the comparison is
   invertible.

## Main results

* `AlgebraicGeometry.isZero_homologyFunctor_derivedGlobalSectionsOver_of_isStrictlyGE` — the
  cohomology of `RΓ(X, K)` vanishes below the bound of a bounded below complex with
  `Γ`-acyclic terms.
* `AlgebraicGeometry.isIso_homologyFunctor_map_comparison_comp_derivedGlobalSectionsOver_map` —
  the comparison composed with `RΓ` of a map is an isomorphism on `H^r` whenever termwise global
  sections of that map is a quasi-isomorphism in degree `r` and the comparison is invertible at
  its target.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_of_isDerivedLimit` — **the limit
  argument**, for an arbitrary scheme over `A` and an arbitrary complex which is the derived limit
  of a tower of bounded below complexes with `Γ`-acyclic terms computing its truncations.
* `AlgebraicGeometry.quasiIso_globalSectionsOver_map_of_tilde_truncGE` — termwise global sections
  inverts a quasi-isomorphism from `\widetilde{(\tau_{\geq -n}M)}^\bullet` to a bounded below
  complex with `Γ`-acyclic terms.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_of_isDerivedLimit` —
  **unbounded affine vanishing for `M̃^•`, granted that `Q(M̃^•)` is the derived limit of a tower
  resolving the truncations.**

The limit argument itself needs neither affineness nor quasi-coherence: it is stated for a scheme
`X` over `A` and a complex `K` of `𝒪_X`-modules, the geometry entering only through the
hypotheses that the tower has `Γ`-acyclic terms and that `K` is the derived limit. Affineness is
used in the final corollary, through Serre vanishing, to see that the sheafified truncations have
`Γ`-acyclic terms.

## What is not done

The hypothesis of the main theorem is the affine case of Stacks 08D3, `E = R\lim \tau_{\geq -n}E`
for `E ∈ D_{QCoh}(\mathcal{O}_{\operatorname{Spec} R})`, and it is *not* proved here. It is not a
missing instance: products in `D(\mathcal{O}_X)` do exist, by
`Stacks.Injectives.hasProducts_derivedCategory` for a Grothendieck abelian category, and the
derived limit of the tower therefore exists. What is needed is that the canonical map into it is
an isomorphism, i.e. that `H^r` commutes with the countable product of the tower — exactly the
step the inexactness of products of sheaves of modules blocks. Stacks proves it by descending to
a basis of affine opens (Cohomology, Lemma 20.37.9, resting on Spaltenstein's local criterion
0D63).

That statement *is* formalized: it is `AlgebraicGeometry.isIso_to_isDerivedLimit_truncGETower`
(`Duality/SpaltensteinCriterion/QuasicoherentTruncationConvergence.lean`, carrying
`@[stacks 08D3]`), with the derived-limit repackaging
`AlgebraicGeometry.isDerivedLimit_truncGETower` in
`Duality/AffineVanishing/UpperBounds.lean`. What still separates it from the hypothesis below is only the model: both
of those are stated at `CategoryTheory.HasDerivedCategory.standard`, which is the model the local
convergence criterion of Stacks 0D6P is available at, whereas everything in this file is at the
locally small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and `HasDerivedCategory`
carries the localized category as data, so the two are different types. Re-binding the convergence
chain at a free `[HasDerivedCategory.{w}]` binder — or re-proving 0D6P there — is what remains.

No `@[stacks 08D4]` attribute appears below, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/AffineVanishingUnbounded.lean`: that tag's covering set is
complete in `StacksFrontier/AlgebraicGeometry/Duality/AffineVanishing/DerivedBounds.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/DerivedAmplitude/UpperBounds.lean`, and what is proved
here is an implication from Stacks 08D3 rather than one of its clauses. Nor is `@[stacks 08D3]`
placed, which stays on `AlgebraicGeometry.isIso_to_isDerivedLimit_truncGETower` in
`Duality/SpaltensteinCriterion/QuasicoherentTruncationConvergence.lean` and is the hypothesis
taken here, nor `@[stacks 090Y]`, which stays on
`CochainComplex.exists_quasiIso_isKInjective` and
`CochainComplex.isIso_of_isDerivedLimit_of_eventually_isIso_homologyMap`.

## Implementation notes

The tower of truncations is presented through a tower of resolutions `𝓘` of the *sheafified*
algebraic truncations `\widetilde{(\tau_{\geq -n}M)}^\bullet` rather than through the truncations
`\tau_{\geq -n}(\widetilde{M}^\bullet)` of the sheafification. The two are isomorphic — `{}^\sim`
is exact — but the first spelling is the one that needs no compatibility of
`Functor.mapHomologicalComplex` with `HomologicalComplex.truncGE`, which Mathlib does not have:
the cone maps are then `{}^\sim` applied to the algebraic `πTruncGE`, and termwise global
sections carries them to the algebraic `πTruncGE` itself by naturality of
`AlgebraicGeometry.tildeGlobalSectionsComplexUnit`.

## References

* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 090Y](https://stacks.math.columbia.edu/tag/090Y)
* [Stacks Project, Tag 070M](https://stacks.math.columbia.edu/tag/070M)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  DerivedCategory

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### Derived global sections of a bounded below complex with acyclic terms -/

/-- **The cohomology of `RΓ(X, K)` vanishes below the bound of `K`.** If `K` is a cochain complex
of `𝒪_X`-modules which is strictly `≥ m` and whose terms are right acyclic for `A`-linear global
sections, then `Hʳ(RΓ(X, Q(K))) = 0` for `r < m`.

Leray's acyclicity lemma identifies `RΓ(X, Q(K))` with `Q(Γ(X, K))`, and `Γ(X, K)` is again
strictly `≥ m`, global sections being applied degreewise. -/
theorem isZero_homologyFunctor_derivedGlobalSectionsOver_of_isStrictlyGE
    (K : CochainComplex X.Modules ℤ) (m : ℤ) (hK : K.IsStrictlyGE m)
    (hac : ∀ i : ℤ, (globalSectionsOver f).rightAcyclic (K.X i)) (r : ℤ) (hr : r < m) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).obj
      ((derivedGlobalSectionsOver f).obj (DerivedCategory.Q.obj K))) := by
  have := hK
  have hiso := isIso_globalSectionsComplexComparison_of_plus_of_rightAcyclic f K ⟨m, hK⟩ hac
  have hGE : CochainComplex.IsStrictlyGE
      (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m :=
    inferInstance
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).mapIso
    (asIso (globalSectionsComplexComparison f K))).symm
  exact (CochainComplex.isZero_of_isGE
      (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m r hr).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) r).app _)

/-- **The comparison, composed with `RΓ` of a map of complexes.** Let `φ : K ⟶ L` be a morphism of
cochain complexes of `𝒪_X`-modules at whose target the comparison
`Q(Γ(X, -)) ⟶ RΓ(X, Q(-))` is invertible. Then the composite
`Q(Γ(X, K)) ⟶ RΓ(X, Q(K)) ⟶ RΓ(X, Q(L))` of the comparison at `K` with `RΓ(X, Q(φ))` is an
isomorphism on `Hʳ` as soon as `Γ(X, φ)` is a quasi-isomorphism in degree `r`.

This is naturality of the comparison: the composite equals `Q(Γ(X, φ))` followed by the
comparison at `L`. -/
theorem isIso_homologyFunctor_map_comparison_comp_derivedGlobalSectionsOver_map
    {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L)
    (hL : IsIso (globalSectionsComplexComparison f L)) (r : ℤ)
    (hφ : QuasiIsoAt (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
      r) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
      (globalSectionsComplexComparison f K ≫
        (derivedGlobalSectionsOver f).map (DerivedCategory.Q.map φ))) := by
  have hnat := (globalSectionsComplexComparisonNatTrans f).naturality φ
  rw [globalSectionsComplexComparisonNatTrans_app,
    globalSectionsComplexComparisonNatTrans_app] at hnat
  dsimp only [Functor.comp_map] at hnat
  rw [← hnat, Functor.map_comp]
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
      (DerivedCategory.Q.map
        (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))) := by
    rw [show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map (DerivedCategory.Q.map
        (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) =
        (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) r).map
          (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) from rfl,
      NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) r)]
    exact (quasiIsoAt_iff_isIso_homologyMap _ r).mp hφ
  infer_instance

/-! ### The limit argument -/

/-- **The `E = R\lim \tau_{\geq -n}E` argument.** Let `X` be a scheme over `A`, let `K` be a
cochain complex of `𝒪_X`-modules and let `E = Q(K)`. Suppose given

* a tower `𝓘 : ℕᵒᵖ ⥤ CochainComplex Mod(𝒪_X) ℤ` whose `n`-th complex is strictly `≥ -n` and has
  terms right acyclic for `A`-linear global sections (for instance: bounded below with injective
  terms);
* maps `φ n : K ⟶ 𝓘ₙ` such that `Γ(X, φ n)` is a quasi-isomorphism in every degree `r ≥ -n`,
  which is what it means for `𝓘ₙ` to compute the truncation `τ_{≥ -n}E` after `Γ`;
* a distinguished triangle exhibiting `E` as the derived limit of the tower `𝓘 ⋙ Q`, with the
  cone given by the `φ n`.

Then the comparison `Q(Γ(X, K)) ⟶ RΓ(X, E)` is an isomorphism.

This is the argument of Stacks 08D4 in three steps: `RΓ(X, -)` carries the derived-limit triangle
to a derived-limit triangle in `D(A)` (Stacks 08U1, in the pinned form, so that the projections of
the transported triangle are `RΓ` of the maps `Q(φ n)`); the transported tower is eventually the
constant `Hʳ(Γ(X, K))`, vanishing below `-n` because `Γ(X, 𝓘ₙ)` is strictly `≥ -n` and agreeing
with `Hʳ(Γ(X, K))` from `n ≥ -r` on because the comparison is invertible at `𝓘ₙ` (Leray) and
`Γ(X, φ n)` is a quasi-isomorphism there; and a derived limit of such a tower is the source of
its cone (Stacks 090Y). -/
theorem isIso_globalSectionsComplexComparison_of_isDerivedLimit
    (K : CochainComplex X.Modules ℤ) (𝓘 : ℕᵒᵖ ⥤ CochainComplex X.Modules ℤ)
    (hGE : ∀ n : ℕ, CochainComplex.IsStrictlyGE (𝓘.obj ⟨n⟩) (-(n : ℤ)))
    (hac : ∀ (n : ℕ) (i : ℤ), (globalSectionsOver f).rightAcyclic ((𝓘.obj ⟨n⟩).X i))
    (φ : ∀ n : ℕ, K ⟶ 𝓘.obj ⟨n⟩)
    (hφ : ∀ (n : ℕ) (r : ℤ), -(n : ℤ) ≤ r →
      QuasiIsoAt (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map (φ n)) r)
    [HasProduct fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩]
    (p : DerivedCategory.Q.obj K ⟶ ∏ᶜ fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) ⟶
      (DerivedCategory.Q.obj K)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) (n + 1) ≫
            (𝓘 ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory X.Modules))
    (hc : ∀ n : ℕ, p ≫ Pi.π (fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) n =
      DerivedCategory.Q.map (φ n)) :
    IsIso (globalSectionsComplexComparison f K) := by
  obtain ⟨hprod, δ', hT'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (globalSectionsOver f) (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (𝓘 ⋙ DerivedCategory.Q) _ p ⟨δ, hT⟩
  set Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n : ℕ =>
    (derivedGlobalSectionsOver f).obj ((𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩)
  set τ : ∀ n : ℕ, Y (n + 1) ⟶ Y n := fun n =>
    (derivedGlobalSectionsOver f).map
      ((𝓘 ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)).op)
  set q : (derivedGlobalSectionsOver f).obj (DerivedCategory.Q.obj K) ⟶ ∏ᶜ Y :=
    (derivedGlobalSectionsOver f).map p ≫
      piComparison (derivedGlobalSectionsOver f)
        (fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) with hq
  -- the comparison at each `𝓘ₙ` is invertible: bounded below with acyclic terms
  have hcompₙ : ∀ n : ℕ, IsIso (globalSectionsComplexComparison f (𝓘.obj ⟨n⟩)) :=
    fun n => isIso_globalSectionsComplexComparison_of_plus_of_rightAcyclic f
      (𝓘.obj ⟨n⟩) ⟨-(n : ℤ), hGE n⟩ (hac n)
  -- the projections of the transported triangle are `RΓ(Q(φ n))`
  have hqπ : ∀ n : ℕ, q ≫ Pi.π Y n =
      (derivedGlobalSectionsOver f).map (DerivedCategory.Q.map (φ n)) := by
    intro n
    rw [hq, Category.assoc, piComparison_comp_π, ← Functor.map_comp, hc n]
  refine CochainComplex.isIso_of_isDerivedLimit_of_eventually_isIso_homologyMap Y τ
    (v := fun n => globalSectionsComplexComparison f K ≫ q ≫ Pi.π Y n)
    (fun n => ?_) _ q δ' hT' (Pi.hom_ext _ _ fun n => by rw [Category.assoc, Pi.lift_comp_π])
    (fun r => (-r).toNat) (fun r n hn => ?_) (fun r n hn => ?_)
  · -- the cone is compatible with the transition maps
    have h0 : q ≫ (Pi.lift fun n : ℕ => Pi.π Y n - Pi.π Y (n + 1) ≫ τ n) = 0 :=
      comp_distTriang_mor_zero₁₂ _ hT'
    have h1 := h0 =≫ Pi.π Y n
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, zero_comp, sub_eq_zero] at h1
    simp only [Category.assoc]
    rw [← h1]
  · -- below the bound the tower vanishes
    exact isZero_homologyFunctor_derivedGlobalSectionsOver_of_isStrictlyGE f
      (𝓘.obj ⟨n⟩) (-(n : ℤ)) (hGE n) (hac n) r (by omega)
  · -- above the bound the cone is a cohomology isomorphism
    rw [hqπ n]
    exact isIso_homologyFunctor_map_comparison_comp_derivedGlobalSectionsOver_map f
      (φ n) (hcompₙ n) r (hφ n r (by omega))

/-! ### The complexes `M̃^•` and their truncations -/

variable (R : CommRingCat.{u})

/-- **Termwise global sections inverts a resolution of a sheafified truncation.** Let `M^•` be a
cochain complex of `R`-modules, `N` a bounded below cochain complex of `𝒪_{Spec R}`-modules with
`Γ`-acyclic terms, and `g : (τ_{≥ m}M)^\sim ⟶ N` a quasi-isomorphism. Then `Γ(Spec R, g)` is a
quasi-isomorphism.

Both complexes are bounded below with terms that are right acyclic for global sections — those of
the source are quasi-coherent, being sheafifications — so this is Leray's acyclicity lemma in the
form of Stacks 05T8. -/
theorem quasiIso_globalSectionsOver_map_of_tilde_truncGE
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : CochainComplex (Spec R).Modules ℤ)
    (hN : N.IsStrictlyGE m) (hacN : ∀ i : ℤ, (globalSectionsOver (𝟙 (Spec R))).rightAcyclic
      (N.X i))
    (g : ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (M.truncGE m) ⟶ N)
    (hg : QuasiIso g) :
    QuasiIso (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := by
  have := hg
  have hsource : CochainComplex.IsStrictlyGE
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (M.truncGE m)) m :=
    inferInstance
  exact Functor.RightAcyclicCriterion.map_quasiIso (globalSectionsOver (𝟙 (Spec R)))
    ((globalSectionsOver (𝟙 (Spec R))).rightAcyclic)
    (exists_mono_rightAcyclic_globalSectionsOver (𝟙 (Spec R)))
    (fun S hS h₁ h₂ =>
      rightAcyclic_X₃_and_shortExact_map_globalSectionsOver (𝟙 (Spec R)) S hS h₁ h₂)
    g ⟨m, hsource⟩ ⟨m, hN⟩
    (fun i => rightAcyclic_globalSectionsOver_of_isQuasicoherent (𝟙 (Spec R))
      ((tilde.functor R).obj ((M.truncGE m).X i)))
    hacN

/-- **Termwise global sections of the sheafified canonical map to a truncation.** For a cochain
complex `M^•` of `R`-modules, `Γ(Spec R, (π : M^• ⟶ τ_{≥ m}M^•)^\sim)` is a quasi-isomorphism in
every degree `r ≥ m`: it *is* the canonical map `π` itself, up to the isomorphism
`𝟭 ≅ (-)^\sim ⋙ Γ(Spec R, -)` of `AlgebraicGeometry.tildeGlobalSectionsComplexUnit`. -/
theorem quasiIsoAt_globalSectionsOver_map_tilde_map_πTruncGE
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (m r : ℤ) (hr : m ≤ r) :
    QuasiIsoAt (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (M.πTruncGE m))) r := by
  have hnat := (tildeGlobalSectionsComplexUnit R).naturality (M.πTruncGE m)
  dsimp only [Functor.id_map, Functor.comp_map] at hnat
  have : IsIso ((tildeGlobalSectionsComplexUnit R).app M) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso ((tildeGlobalSectionsComplexUnit R).app (M.truncGE m)) :=
    NatIso.isIso_app_of_isIso _ _
  have := M.quasiIsoAt_πTruncGE m r hr
  have : QuasiIsoAt ((tildeGlobalSectionsComplexUnit R).app M ≫
      ((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (M.πTruncGE m))) r := by
    rw [← hnat]
    infer_instance
  exact quasiIsoAt_of_comp_left ((tildeGlobalSectionsComplexUnit R).app M) _ r

/-! ### Unbounded affine vanishing from the derived limit of the truncations -/

/-- **Unbounded affine vanishing, granted the affine case of Stacks 08D3.** Let `M^•` be a cochain
complex of `R`-modules and let `E = Q(M̃^•)`. Suppose given

* a tower `𝓘 : ℕᵒᵖ ⥤ CochainComplex Mod(𝒪_{Spec R}) ℤ` whose `n`-th term is strictly `≥ -n` and
  has terms right acyclic for global sections (for instance: bounded below with injective terms);
* quasi-isomorphisms `g n : (τ_{≥ -n}M)^\sim ⟶ 𝓘ₙ`, so that `𝓘ₙ` represents `τ_{≥ -n}E`;
* a distinguished triangle exhibiting `E` as the derived limit of `𝓘 ⋙ Q` whose cone is the
  canonical one, i.e. whose projections are the images of the maps
  `M̃^• ⟶ (τ_{≥ -n}M)^\sim ⟶ 𝓘ₙ`.

Then the comparison `Q(Γ(Spec R, M̃^•)) ⟶ RΓ(E)` is an isomorphism: that is unbounded affine
vanishing for `M^•`, the hypothesis of
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app`.

The third hypothesis is the affine case of Stacks 08D3 in the shape Stacks 070F and 070M deliver
it; it is the one thing not proved in this development. Everything else is the `E = R\lim
\tau_{\geq -n}E` argument of Stacks 08D4: `RΓ` carries the derived limit to a derived limit
(Stacks 08U1), the resulting tower in `D(R)` is eventually the constant `Hʳ(Γ(Spec R, M̃^•))`
because each `𝓘ₙ` is bounded below with acyclic terms, and a derived limit of such a tower is
the source of its cone (Stacks 090Y). -/
theorem isIso_globalSectionsComplexComparison_tilde_of_isDerivedLimit
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (𝓘 : ℕᵒᵖ ⥤ CochainComplex (Spec R).Modules ℤ)
    (hGE : ∀ n : ℕ, (𝓘.obj ⟨n⟩).IsStrictlyGE (-(n : ℤ)))
    (hac : ∀ (n : ℕ) (i : ℤ),
      (globalSectionsOver (𝟙 (Spec R))).rightAcyclic ((𝓘.obj ⟨n⟩).X i))
    (g : ∀ n : ℕ, ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (M.truncGE (-(n : ℤ))) ⟶ 𝓘.obj ⟨n⟩)
    (hg : ∀ n : ℕ, QuasiIso (g n))
    [HasProduct fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩]
    (p : DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ⟶
      ∏ᶜ fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) ⟶
      (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) (n + 1) ≫
            (𝓘 ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory (Spec R).Modules))
    (hc : ∀ n : ℕ, p ≫ Pi.π (fun n : ℕ => (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) n =
      DerivedCategory.Q.map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (M.πTruncGE (-(n : ℤ))) ≫ g n)) :
    IsIso (globalSectionsComplexComparison (𝟙 (Spec R))
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := by
  refine isIso_globalSectionsComplexComparison_of_isDerivedLimit (𝟙 (Spec R)) _ 𝓘 hGE hac
    (fun n => ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (M.πTruncGE (-(n : ℤ))) ≫ g n) (fun n r hr => ?_) p δ hT hc
  have := quasiIsoAt_globalSectionsOver_map_tilde_map_πTruncGE R M (-(n : ℤ)) r hr
  have := quasiIso_globalSectionsOver_map_of_tilde_truncGE R M (-(n : ℤ)) (𝓘.obj ⟨n⟩)
    (hGE n) (hac n) (g n) (hg n)
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry

end
