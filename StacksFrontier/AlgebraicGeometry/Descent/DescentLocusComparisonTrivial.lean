module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusComparisonCore
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# The topological step of Tag 0BF1

The affine core `AlgebraicGeometry.DescentLocusComparison.exists_vanishing_family` produces a
section of `L` over the closed subscheme `V(c) ∩ D(g)` of `Spec A` which is nonzero on the fibre
of the point. This file carries out the step the source calls "a straightforward topological
argument (omitted)": the nonvanishing locus of that section is open
([Stacks, Tag 01CY]) and contains the fibre, because a nonzero global section of the trivial
module on a fibre with `Γ(𝒪) = κ` is a unit; the image under the proper projection of its
complement is closed and misses the point; so after shrinking to a basic open the section
generates `L`, and `L` is trivial after every base change to `V(c) ∩ D(g)`.

## Main results

* `AlgebraicGeometry.DescentLocusComparison.nonempty_iso_unit_of_nonvanishingLocus_eq_univ`
* `AlgebraicGeometry.DescentLocusComparison.exists_vanishing_family_trivial`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.DescentLocusComparison

/-- **An invertible module with a nowhere vanishing global section is trivial** ([Stacks,
Tag 01CY]). -/
theorem nonempty_iso_unit_of_nonvanishingLocus_eq_univ {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] (s : Γ(M, ⊤))
    (hs : Stacks.Ample.nonvanishingLocus M s = Set.univ) :
    Nonempty (M ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  have hiso := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ M
    ((Stacks.NonvanishingSpelling.sectionsEquiv Y M).symm s)
    ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq Y M s).trans hs)
  exact ⟨(asIso (M.unitHomEquiv.symm
    ((Stacks.NonvanishingSpelling.sectionsEquiv Y M).symm s))).symm⟩

/-- **A nonzero global section of the trivial module on a scheme whose ring of global functions
is a field vanishes nowhere.** -/
theorem nonvanishingLocus_eq_univ_of_ne_zero {K : Type u} [Field K] {Y : Scheme.{u}}
    {h : Y ⟶ Spec (.of K)} (hΓ : Function.Bijective (Stacks.Cech.baseRingHom h ⊤).hom)
    {M : Y.Modules} (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) (s : Γ(M, ⊤)) (hs : s ≠ 0) :
    Stacks.Ample.nonvanishingLocus M s = Set.univ := by
  set τ : Γ(Y, ⊤) := e.hom.app ⊤ s
  have hτ : τ ≠ 0 := by
    intro h0
    apply hs
    rw [← Stacks.Cech.iso_inv_app_hom_app e ⊤ s]
    change e.inv.app ⊤ τ = 0
    rw [h0]
    exact map_zero _
  obtain ⟨k, hk⟩ := hΓ.2 τ
  have hk0 : k ≠ 0 := fun h0 => hτ (by rw [← hk, h0, map_zero])
  have hu : IsUnit τ := hk ▸ (isUnit_iff_ne_zero.mpr hk0).map _
  let one : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) := (1 : Γ(Y, ⊤))
  have h1 : Stacks.Ample.nonvanishingLocus (SheafOfModules.unit Y.ringCatSheaf) one =
      Set.univ :=
    Set.eq_univ_of_forall fun x => Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one Y x one rfl
  have key := Stacks.Ample.nonvanishingLocus_smul (SheafOfModules.unit Y.ringCatSheaf) τ one
  rw [h1, Y.basicOpen_of_isUnit hu] at key
  rw [← Stacks.Ample.nonvanishingLocus_congr e s]
  convert key using 2
  · exact (mul_one τ).symm
  · simp

section Trivial

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} (a : X' ⟶ X)
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A)) (ha : a ≫ f = f')
  [IsProper f] [LocallyOfFinitePresentation f] [IsProper f'] [LocallyOfFinitePresentation f']
  (L : X.Modules) [L.IsFinitePresentation]
  [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
  (hL : IsFlatOver f.toLRSHom.toShHom L)
  (hL' : IsFlatOver f'.toLRSHom.toShHom ((Scheme.Modules.pullback a).obj L))

include ha hL hL' in
/-- **The affine form of [Stacks, Tag 0BF1].** In the situation of `exists_vanishing_family`,
with `L` invertible, there are `g` with `χ₀ g ≠ 0` and finitely many `c_k` with `χ₀ c_k = 0`
such that for every `A`-algebra `B` in which `g` is invertible:

* if the base change of `a^* L` to `X'_B` is trivial and `Γ(X'_B, 𝒪) = B`, then every `c_k`
  vanishes in `B`;
* if every `c_k` vanishes in `B`, then the base change of `L` to `X_B` is trivial.

The second clause is the source's closing "straightforward topological argument": the section
of `L` over `V(c) ∩ D(g)` produced by `exists_vanishing_family` vanishes nowhere on the fibre, its
nonvanishing locus is open, and the image of the complement under the proper projection is a
closed set missing the point, so a basic open neighbourhood of the point avoids it. -/
theorem exists_vanishing_family_trivial {K₀ : Type u} [Field K₀] (χ₀ : A →+* K₀)
    {X₀ X'₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of K₀)} {f'₀ : X'₀ ⟶ Spec (.of K₀)}
    {q₀ : X₀ ⟶ X} {q'₀ : X'₀ ⟶ X'}
    (hsq₀ : IsPullback q₀ f₀ f (Spec.map (CommRingCat.ofHom χ₀)))
    (hsq'₀ : IsPullback q'₀ f'₀ f' (Spec.map (CommRingCat.ofHom χ₀)))
    (a₀ : X'₀ ⟶ X₀) (ha₀ : a₀ ≫ f₀ = f'₀) (hcomm : a₀ ≫ q₀ = q'₀ ≫ a)
    (hL₀ : Nonempty ((Scheme.Modules.pullback q₀).obj L ≅ SheafOfModules.unit X₀.ringCatSheaf))
    (hΓ₀ : Function.Bijective (Stacks.Cech.baseRingHom f₀ ⊤).hom)
    (hΓ'₀ : Function.Bijective (Stacks.Cech.baseRingHom f'₀ ⊤).hom)
    (hH1 : Function.Injective (Stacks.Cohomology.moduleCohomologyPullbackMap
      a₀.toLRSHom.toShHom 1 (SheafOfModules.unit X₀.ringCatSheaf))) :
    ∃ g : A, χ₀ g ≠ 0 ∧ ∃ (n : ℕ) (c : Fin n → A), (∀ k, χ₀ (c k) = 0) ∧
      (∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ g) →
        ∀ {Y' : Scheme.{u}} {p' : Y' ⟶ X'} {h' : Y' ⟶ Spec (.of B)},
          IsPullback p' h' f' (Spec.map (CommRingCat.ofHom φ)) →
          Function.Bijective (Stacks.Cech.baseRingHom h' ⊤).hom →
          Nonempty ((Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback a).obj L) ≅
            SheafOfModules.unit Y'.ringCatSheaf) →
          ∀ k, φ (c k) = 0) ∧
      (∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ g) → (∀ k, φ (c k) = 0) →
        ∀ {Y : Scheme.{u}} {p : Y ⟶ X} {h : Y ⟶ Spec (.of B)},
          IsPullback p h f (Spec.map (CommRingCat.ofHom φ)) →
          Nonempty ((Scheme.Modules.pullback p).obj L ≅ SheafOfModules.unit Y.ringCatSheaf)) := by
  classical
  obtain ⟨g, hg, n, c, hc, hI, hII⟩ := exists_vanishing_family a f f' ha L hL hL' χ₀ hsq₀ hsq'₀
    a₀ ha₀ hcomm hL₀ hΓ₀ hΓ'₀ hH1
  obtain ⟨e₀⟩ := hL₀
  -- the universal algebra `B₀ = (A ⧸ (c))_g`
  set J : Ideal A := Ideal.span (Set.range c)
  set π : A →+* A ⧸ J := Ideal.Quotient.mk J
  set B₀ := Localization.Away (π g)
  set φ₀ : A →+* B₀ := (algebraMap (A ⧸ J) B₀).comp π
  have hφ₀g : IsUnit (φ₀ g) := IsLocalization.Away.algebraMap_isUnit (π g)
  have hφ₀c : ∀ k, φ₀ (c k) = 0 := fun k => by
    change algebraMap (A ⧸ J) B₀ (π (c k)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self k)), map_zero]
  -- every algebra in which `g` is invertible and the `c_k` vanish is a `B₀`-algebra
  have hfac : ∀ (B : Type u) [CommRing B] (φ : A →+* B), IsUnit (φ g) → (∀ k, φ (c k) = 0) →
      ∃ ψ : B₀ →+* B, ψ.comp φ₀ = φ := by
    intro B _ φ hφg hφc
    have hJ : J ≤ RingHom.ker φ := Ideal.span_le.2 (Set.range_subset_iff.2 hφc)
    let ψR : A ⧸ J →+* B := Ideal.Quotient.lift J φ fun x hx => hJ hx
    have hu : IsUnit (ψR (π g)) := hφg
    refine ⟨IsLocalization.Away.lift (π g) hu, RingHom.ext fun x => ?_⟩
    change IsLocalization.Away.lift (π g) hu (algebraMap (A ⧸ J) B₀ (π x)) = φ x
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.lift_mk J φ _
  obtain ⟨ψ₀, hψ₀⟩ := hfac K₀ χ₀ (isUnit_iff_ne_zero.mpr hg) hc
  -- the base change to `B₀` and its section
  set Y₀ := pullback f (Spec.map (CommRingCat.ofHom φ₀))
  have hsqY₀ : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ₀)))
      (pullback.snd f (Spec.map (CommRingCat.ofHom φ₀))) f
      (Spec.map (CommRingCat.ofHom φ₀)) := IsPullback.of_hasPullback _ _
  set p₀ := pullback.fst f (Spec.map (CommRingCat.ofHom φ₀))
  set h₀ := pullback.snd f (Spec.map (CommRingCat.ofHom φ₀))
  set L₀ := (Scheme.Modules.pullback p₀).obj L with hL₀def
  obtain ⟨σ, hσ⟩ := hII B₀ φ₀ hφ₀g hφ₀c hsqY₀
  set N := Stacks.Ample.nonvanishingLocus L₀ σ
  have hNopen : IsOpen N := Stacks.NonvanishingOpen.isOpen_nonvanishingLocus Y₀ L₀ σ
  set Zc := h₀.base '' Nᶜ
  have hZc : IsClosed Zc := h₀.isClosedMap _ hNopen.isClosed_compl
  -- maps into the base change `Y₀` over a `B₀`-algebra `B`
  have hlift : ∀ (B : Type u) [CommRing B] (φ : A →+* B) (ψ : B₀ →+* B), ψ.comp φ₀ = φ →
      ∀ {Y : Scheme.{u}} {p : Y ⟶ X} {h : Y ⟶ Spec (.of B)},
        IsPullback p h f (Spec.map (CommRingCat.ofHom φ)) →
        ∃ j : Y ⟶ Y₀, j ≫ p₀ = p ∧ IsPullback j h h₀ (Spec.map (CommRingCat.ofHom ψ)) := by
    intro B _ φ ψ hψ Y p h hsq
    subst hψ
    have hSpec : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ₀) =
        Spec.map (CommRingCat.ofHom (ψ.comp φ₀)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact ⟨hsqY₀.lift p (h ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [Category.assoc, hSpec]; exact hsq.w), hsqY₀.lift_fst _ _ _,
      IsPullback.of_right (by rwa [hsqY₀.lift_fst, hSpec]) (hsqY₀.lift_snd _ _ _) hsqY₀⟩
  obtain ⟨r, hr1, hsqr⟩ := hlift K₀ χ₀ ψ₀ hψ₀ hsq₀
  have hσr := hσ K₀ ψ₀ hsqr
  -- the section vanishes nowhere on the fibre
  let eR : (Scheme.Modules.pullback r).obj L₀ ≅ SheafOfModules.unit X₀.ringCatSheaf :=
    (Scheme.Modules.pullbackComp r p₀).app L ≪≫ (Scheme.Modules.pullbackCongr hr1).app L ≪≫ e₀
  have hfib : r.base ⁻¹' N = Set.univ := by
    rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus r L₀ σ]
    exact nonvanishingLocus_eq_univ_of_ne_zero hΓ₀ eR _
      (show Stacks.NonvanishingPullback.pullbackGlobalSection r L₀ σ ≠ 0 from hσr)
  -- a basic open neighbourhood of the point avoiding the bad locus
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of K₀)) := inferInstance
  set s₀ := (Spec.map (CommRingCat.ofHom ψ₀)).base ξ
  have hs₀ : s₀ ∉ Zc := by
    rintro ⟨x, hxN, hx⟩
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hsqr x ξ hx
    exact hxN (hy ▸ (Set.ext_iff.1 hfib y).2 trivial)
  obtain ⟨_, ⟨t, rfl⟩, hst, htZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hs₀ hZc.isOpen_compl
  obtain ⟨⟨rt, ⟨_, ⟨m, rfl⟩⟩⟩, hrt⟩ := IsLocalization.mk'_surjective (Submonoid.powers (π g)) t
  obtain ⟨a₁, rfl⟩ := Ideal.Quotient.mk_surjective rt
  have hspec : t * φ₀ (g ^ m) = φ₀ a₁ := by
    rw [← hrt]
    change IsLocalization.mk' B₀ (π a₁) ⟨π g ^ m, _⟩ * algebraMap (A ⧸ J) B₀ (π (g ^ m)) = _
    rw [map_pow π]
    exact IsLocalization.mk'_spec B₀ (π a₁) ⟨π g ^ m, _⟩
  have hψt : ψ₀ t ≠ 0 := fun h0 => hst (Ideal.mem_comap.2 (h0 ▸ ξ.asIdeal.zero_mem))
  refine ⟨g * a₁, ?_, n, c, hc, fun B _ φ hφ => hI B φ
    (isUnit_of_mul_isUnit_left (by rwa [map_mul] at hφ)), ?_⟩
  · have h1 := congrArg ψ₀ hspec
    rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hψ₀] at h1
    rw [map_mul, ← h1, map_pow]
    exact mul_ne_zero hg (mul_ne_zero hψt (pow_ne_zero _ hg))
  · intro B _ φ hφ hφc Y p h hsq
    rw [map_mul] at hφ
    obtain ⟨ψ, hψ⟩ := hfac B φ (isUnit_of_mul_isUnit_left hφ) hφc
    obtain ⟨j, hj1, hsqj⟩ := hlift B φ ψ hψ hsq
    have hψt' : IsUnit (ψ t) := by
      have h1 := congrArg ψ hspec
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hψ] at h1
      have hu : IsUnit (φ a₁) := isUnit_of_mul_isUnit_right hφ
      rw [← h1] at hu
      exact isUnit_of_mul_isUnit_left hu
    have hall : j.base ⁻¹' N = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      by_contra hy
      apply htZ (show h₀.base (j.base y) ∈ PrimeSpectrum.basicOpen t from ?_) ⟨j.base y, hy, rfl⟩
      rw [← Scheme.Hom.comp_apply, hsqj.w, Scheme.Hom.comp_apply]
      change t ∉ Ideal.comap ψ (h.base y).asIdeal
      rw [Ideal.mem_comap]
      exact fun hmem => (h.base y).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hψt')
    rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus j L₀ σ] at hall
    obtain ⟨e⟩ := nonempty_iso_unit_of_nonvanishingLocus_eq_univ _ _ hall
    exact ⟨((Scheme.Modules.pullbackCongr hj1).app L).symm ≪≫
      ((Scheme.Modules.pullbackComp j p₀).app L).symm ≪≫ e⟩

end Trivial

end AlgebraicGeometry.DescentLocusComparison

end
