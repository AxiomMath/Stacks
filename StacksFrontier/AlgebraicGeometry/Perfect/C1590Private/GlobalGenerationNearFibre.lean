module

public import StacksFrontier.AlgebraicGeometry.Perfect.C1590Private.KernelModelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.C1590Private.NonvanishingGeneration
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible

/-!
# Global generation near a fibre over a reduced base

Let `A` be a reduced ring, `f : X ⟶ Spec A` proper and of finite presentation and `F` an
`𝒪_X`-module of finite presentation flat over `A`. Let `p` be a prime of `A` such that
`dim Γ(X_q, F_q) ≥ dim Γ(X_p, F_p)` for every prime `q`. Then near `p` the global sections of `F`
commute with every base change and are free of rank `dim Γ(X_p, F_p)`
(`AlgebraicGeometry.C1590Private.exists_away_free_sections_of_finrank_le`): in the kernel model of
cohomology and base change the matrix vanishes modulo every prime near `p`, hence vanishes on a
reduced base. This is the step of the proof of Stacks 0E6Y which the source takes from cohomology
and base change (Stacks 0CTM, 0E6A).

## Main results

* `AlgebraicGeometry.C1590Private.exists_away_free_sections_of_finrank_le`: the sections of base
  changes near `p` are free on a fixed basis, naturally in the base change.
* `AlgebraicGeometry.C1590Private.exists_away_nonempty_generatingSections`: for `F` invertible
  and `F_p` globally generated, the fibres of `F` near `p` are globally generated.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.C1590Private

section FreeSections

/-- A ring map whose kernel is a prime `p` does not kill an element outside `p`. -/
private theorem map_ne_zero_of_ker_eq {A K : Type*} [CommRing A] [Semiring K] {φ : A →+* K}
    {p : Ideal A} (hφ : RingHom.ker φ = p) {g : A} (hg : g ∉ p) : φ g ≠ 0 :=
  fun h => hg (hφ ▸ RingHom.mem_ker.2 h)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- **Near a point of minimal fibre rank over a reduced base, the global sections of every base
change are free on a fixed basis.** Let `A` be reduced, `f : X ⟶ Spec A` proper and of finite
presentation and `F` of finite presentation and flat over `A`, and let `p` be a prime with
`dim Γ(X_p, F_p) ≤ r₀ ≤ dim Γ(X_q, F_q)` for every prime `q`, each fibre being read at some field
point over the prime. Then there are `g ∉ p` and `r` such
that for every `A`-algebra `B` in which `g` is invertible and every cartesian square exhibiting
`X'` as `X ×_A B`, the `B`-module `Γ(X', F_{X'})` is identified with `B^r`, naturally in `B`. -/
theorem exists_away_free_sections_of_finrank_le [_root_.IsReduced A] [IsProper f]
    [LocallyOfFinitePresentation f] [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (p : Ideal A) [p.IsPrime] (r₀ : ℕ)
    (hp : ∃ (K : Type u) (_ : Field K) (φ : A →+* K) (_ : RingHom.ker φ = p) (Xp : Scheme.{u})
      (fp : Xp ⟶ Spec (.of K)) (gp : Xp ⟶ X)
      (_ : IsPullback gp fp f (Spec.map (CommRingCat.ofHom φ))),
        letI := Stacks.Cech.sectionsModule fp ((Scheme.Modules.pullback gp).obj F) ⊤
        Module.finrank K Γ((Scheme.Modules.pullback gp).obj F, ⊤) ≤ r₀)
    (hq : ∀ (q : Ideal A) [q.IsPrime], ∃ (K : Type u) (_ : Field K) (φ : A →+* K)
      (_ : RingHom.ker φ = q) (Xq : Scheme.{u}) (fq : Xq ⟶ Spec (.of K)) (gq : Xq ⟶ X)
      (_ : IsPullback gq fq f (Spec.map (CommRingCat.ofHom φ))),
        letI := Stacks.Cech.sectionsModule fq ((Scheme.Modules.pullback gq).obj F) ⊤
        r₀ ≤ Module.finrank K Γ((Scheme.Modules.pullback gq).obj F, ⊤)) :
    ∃ (g : A) (_ : g ∉ p) (r : ℕ)
      (Φ : ∀ {B : Type u} [CommRing B] (φ : A →+* B) (_ : IsUnit (φ g)) {X' : Scheme.{u}}
          {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
          (_ : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))),
          letI := Stacks.Cech.sectionsModule f' ((Scheme.Modules.pullback g').obj F) ⊤
          (Fin r → B) ≃ₗ[B] Γ((Scheme.Modules.pullback g').obj F, ⊤)),
      ∀ {B B' : Type u} [CommRing B] [CommRing B'] (φ : A →+* B) (ψ : B →+* B')
        (hg : IsUnit (φ g)) {X' X'' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)}
        {f'' : X'' ⟶ Spec (.of B')} {g' : X' ⟶ X} {g'' : X'' ⟶ X'}
        (hsq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ)))
        (hsq' : IsPullback g'' f'' f' (Spec.map (CommRingCat.ofHom ψ))) (v : Fin r → B),
        ((Scheme.Modules.pullbackComp g'' g').hom.app F).app ⊤
            (AlgebraicGeometry.pullbackSectionHom g'' ((Scheme.Modules.pullback g').obj F) ⊤ ⊤
              (by simp) (Φ φ hg hsq v)) =
          Φ (ψ.comp φ) (hg.map ψ)
            (Stacks.Cech.isPullback_comp_specMap φ ψ f f' f'' g' g'' hsq hsq') (ψ ∘ v) := by
  classical
  obtain ⟨g, hg, r, β, D, hDp, Φ, hnat⟩ :=
    exists_away_kernelModel_of_finitePresentation f F hflat p
  have hrank : ∀ {K : Type u} [Field K] (φ : A →+* K) (_ : φ g ≠ 0) {Xq : Scheme.{u}}
      {fq : Xq ⟶ Spec (.of K)} {gq : Xq ⟶ X}
      (hsq : IsPullback gq fq f (Spec.map (CommRingCat.ofHom φ))),
      let := Stacks.Cech.sectionsModule fq ((Scheme.Modules.pullback gq).obj F) ⊤
      Module.finrank K Γ((Scheme.Modules.pullback gq).obj F, ⊤) =
        Module.finrank K (LinearMap.ker (Matrix.mulVecLin (D.map φ))) :=
    fun {K} _ φ hφ Xq fq gq hsq => by
      let := Stacks.Cech.sectionsModule fq ((Scheme.Modules.pullback gq).obj F) ⊤
      exact (Φ φ (isUnit_iff_ne_zero.2 hφ) hsq).finrank_eq.symm
  have hrp : r ≤ r₀ := by
    obtain ⟨K, _, φ, hφ, Xp, fp, gp, hsq, hle⟩ := hp
    have hφg := map_ne_zero_of_ker_eq hφ hg
    have hD0 : D.map φ = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.zero_apply]
      rw [← RingHom.mem_ker, hφ]
      exact hDp i j
    have h := hrank φ hφg hsq
    rw [hD0, Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun] at h
    exact h ▸ hle
  have hDq : ∀ (q : Ideal A) [q.IsPrime], g ∉ q → ∀ i j, D i j ∈ q := by
    intro q _ hgq i j
    obtain ⟨K, _, φ, hφ, Xq, fq, gq, hsq, h1⟩ := hq q
    have hφg := map_ne_zero_of_ker_eq hφ hgq
    rw [hrank φ hφg hsq] at h1
    have h2 : LinearMap.ker (Matrix.mulVecLin (D.map φ)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
        (by rw [Module.finrank_fin_fun]; omega))
    have h3 := congrFun (LinearMap.ext_iff.1 (LinearMap.ker_eq_top.1 h2) (Pi.single j 1)) i
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h3
    rwa [← hφ, RingHom.mem_ker]
  have hDg : ∀ i j, algebraMap A (Localization.Away g) (D i j) = 0 := by
    intro i j
    refine _root_.IsReduced.eq_zero _ ((nilpotent_iff_mem_prime).2 fun P hP => ?_)
    have hgP : g ∉ P.comap (algebraMap A (Localization.Away g)) := fun h =>
      hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit g))
    exact hDq _ hgP i j
  have hD0 : ∀ {B : Type u} [CommRing B] (φ : A →+* B) (_ : IsUnit (φ g)), D.map φ = 0 := by
    intro B _ φ hφ
    ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply]
    rw [← IsLocalization.Away.lift_comp (S := Localization.Away g) g hφ, RingHom.comp_apply,
      hDg, map_zero]
  have hker : ∀ {B : Type u} [CommRing B] (φ : A →+* B) (hφ : IsUnit (φ g)),
      LinearMap.ker (Matrix.mulVecLin (D.map φ)) = ⊤ := fun φ hφ => by
    rw [hD0 φ hφ, Matrix.mulVecLin_zero, LinearMap.ker_zero]
  refine ⟨g, hg, r, fun {B} _ φ hφ X' f' g' hsq =>
    (LinearEquiv.ofTop _ (hker φ hφ)).symm.trans (Φ φ hφ hsq), ?_⟩
  intro B B' _ _ φ ψ hφ X' X'' f' f'' g' g'' hsq hsq' v
  exact hnat φ ψ hφ hsq hsq' ⟨v, by rw [hker φ hφ]; trivial⟩

end FreeSections

/-! ### Invertible modules and pulled back sections -/

/-- The pullback of a global section along the identification `h ⁻¹ ⊤ = ⊤` is
`AlgebraicGeometry.pullbackGlobalSections`. -/
theorem pullbackSectionHom_top_apply {Y Z : Scheme.{u}} (h : Y ⟶ Z) (L : Z.Modules)
    (hle : (⊤ : Y.Opens) ≤ h ⁻¹ᵁ ⊤) (s : Γ(L, ⊤)) :
    pullbackSectionHom h L ⊤ ⊤ hle s = pullbackGlobalSections h L s := by
  show ((Scheme.Modules.pullback h).obj L).presheaf.map (homOfLE hle).op _ =
    ((Scheme.Modules.pullback h).obj L).presheaf.map (eqToHom (by simp)).op _
  congr 2

section InvertibleModule

variable {X : Scheme.{u}}

/-- An invertible module is of finite presentation. -/
theorem isFinitePresentation_of_isInvertibleModule (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] : L.IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_of_isInvertible_ringedSpace X.toRingedSpace L
    ‹_›

/-- An invertible module on a scheme flat over an affine base is flat over the base. -/
theorem isFlatOver_of_isInvertibleModule {A : Type u} [CommRing A] (f : X ⟶ Spec (.of A))
    [Flat f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    IsFlatOver f.toLRSHom.toShHom L := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  exact AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f L

end InvertibleModule

/-! ### Global generation near a fibre -/

section GlobalGeneration

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- **Global generation spreads from a fibre of minimal rank, over a reduced base.** Let `A` be
reduced, `f : X ⟶ Spec A` proper and of finite presentation, `F` invertible, of finite
presentation and flat over `A`, and `p` a prime such that the fibre `F_p` is globally generated
and `dim Γ(X_p, F_p) ≤ r₀ ≤ dim Γ(X_q, F_q)` for every prime `q`, each fibre being read at some
field point over the prime. Then there is `g ∉ p` such that the fibre of `F` at every field point
`φ : A → K` with `φ(g) ≠ 0` is globally generated. -/
theorem exists_away_nonempty_generatingSections [_root_.IsReduced A] [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [Stacks.Ample.IsInvertibleModule X F] (p : Ideal A)
    [p.IsPrime] (r₀ : ℕ)
    (hp : ∃ (K : Type u) (_ : Field K) (φ : A →+* K) (_ : RingHom.ker φ = p) (Xp : Scheme.{u})
      (fp : Xp ⟶ Spec (.of K)) (gp : Xp ⟶ X)
      (_ : IsPullback gp fp f (Spec.map (CommRingCat.ofHom φ))),
        (letI := Stacks.Cech.sectionsModule fp ((Scheme.Modules.pullback gp).obj F) ⊤
        Module.finrank K Γ((Scheme.Modules.pullback gp).obj F, ⊤) ≤ r₀) ∧
          Nonempty ((Scheme.Modules.pullback gp).obj F).GeneratingSections)
    (hq : ∀ (q : Ideal A) [q.IsPrime], ∃ (K : Type u) (_ : Field K) (φ : A →+* K)
      (_ : RingHom.ker φ = q) (Xq : Scheme.{u}) (fq : Xq ⟶ Spec (.of K)) (gq : Xq ⟶ X)
      (_ : IsPullback gq fq f (Spec.map (CommRingCat.ofHom φ))),
        letI := Stacks.Cech.sectionsModule fq ((Scheme.Modules.pullback gq).obj F) ⊤
        r₀ ≤ Module.finrank K Γ((Scheme.Modules.pullback gq).obj F, ⊤)) :
    ∃ g : A, g ∉ p ∧ ∀ {K : Type u} [Field K] (φ : A →+* K), φ g ≠ 0 → ∀ {XK : Scheme.{u}}
      {fK : XK ⟶ Spec (.of K)} {gK : XK ⟶ X},
      IsPullback gK fK f (Spec.map (CommRingCat.ofHom φ)) →
        Nonempty ((Scheme.Modules.pullback gK).obj F).GeneratingSections := by
  classical
  have : F.IsFinitePresentation := isFinitePresentation_of_isInvertibleModule F
  obtain ⟨g, hg, r, Φ, hnat⟩ := exists_away_free_sections_of_finrank_le f F
    (isFlatOver_of_isInvertibleModule f F) p r₀
    (by
      obtain ⟨K, hK, φ, hφ, Xp, fp, gp, hsq, h, -⟩ := hp
      exact ⟨K, hK, φ, hφ, Xp, fp, gp, hsq, h⟩) hq
  set Ag := Localization.Away g
  set α := algebraMap A Ag
  have hα : IsUnit (α g) := IsLocalization.Away.algebraMap_isUnit g
  set Xg := pullback f (Spec.map (CommRingCat.ofHom α))
  set fst := pullback.fst f (Spec.map (CommRingCat.ofHom α))
  set snd := pullback.snd f (Spec.map (CommRingCat.ofHom α))
  have hsqg : IsPullback fst snd f (Spec.map (CommRingCat.ofHom α)) :=
    IsPullback.of_hasPullback _ _
  set Fg := (Scheme.Modules.pullback fst).obj F
  have : Stacks.Ample.IsInvertibleModule Xg Fg :=
    AlgebraicGeometry.SheafOfModules.isInvertible_pullback fst F
  let e : Fin r → Γ(Fg, ⊤) := fun i => Φ α hα hsqg (Pi.single i 1)
  have hbasis : ∀ {B : Type u} [CommRing B] (ψ : Ag →+* B) {X'' : Scheme.{u}}
      {f'' : X'' ⟶ Spec (.of B)} {g'' : X'' ⟶ Xg}
      (hsq' : IsPullback g'' f'' snd (Spec.map (CommRingCat.ofHom ψ))) (i : Fin r) (y : X''),
      y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback (g'' ≫ fst)).obj F)
          (Φ (ψ.comp α) (hα.map ψ)
            (Stacks.Cech.isPullback_comp_specMap α ψ f snd f'' fst g'' hsqg hsq')
            (Pi.single i 1)) ↔
        g'' y ∈ Stacks.Ample.nonvanishingLocus Fg (e i) := by
    intro B _ ψ X'' f'' g'' hsq' i y
    have hv : (ψ ∘ (Pi.single i 1 : Fin r → Ag)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    have h := hnat α ψ hα hsqg hsq' (Pi.single i 1)
    rw [hv] at h
    rw [← h]
    refine (mem_nonvanishingLocus_iso_iff ((Scheme.Modules.pullbackComp g'' fst).app F) _ y).trans
      ?_
    rw [pullbackSectionHom_top_apply]
    exact (Set.ext_iff.1
      (Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections g'' Fg (e i))
        y).symm
  have hspan : ∀ {B : Type u} [CommRing B] (ψ : Ag →+* B) {X'' : Scheme.{u}}
      {f'' : X'' ⟶ Spec (.of B)} {g'' : X'' ⟶ Xg}
      (hsq' : IsPullback g'' f'' snd (Spec.map (CommRingCat.ofHom ψ)))
      (t : Γ((Scheme.Modules.pullback (g'' ≫ fst)).obj F, ⊤)),
      ∃ c : Fin r → Γ(X'', ⊤), t = ∑ i, c i • Φ (ψ.comp α) (hα.map ψ)
            (Stacks.Cech.isPullback_comp_specMap α ψ f snd f'' fst g'' hsqg hsq')
            (Pi.single i 1) := by
    intro B _ ψ X'' f'' g'' hsq' t
    let := Stacks.Cech.sectionsModule f'' ((Scheme.Modules.pullback (g'' ≫ fst)).obj F) ⊤
    set Ψ := Φ (ψ.comp α) (hα.map ψ)
      (Stacks.Cech.isPullback_comp_specMap α ψ f snd f'' fst g'' hsqg hsq')
    refine ⟨fun i => (Stacks.Cech.baseRingHom f'' ⊤).hom (Ψ.symm t i), ?_⟩
    have hsum : Ψ.symm t = ∑ i, Ψ.symm t i • (Pi.single i 1 : Fin r → B) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [← Ψ.apply_symm_apply t, hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have hfib : ∀ {K : Type u} [Field K] (φ : A →+* K) (_ : φ g ≠ 0) {XK : Scheme.{u}}
      {fK : XK ⟶ Spec (.of K)} {gK : XK ⟶ X}
      (_ : IsPullback gK fK f (Spec.map (CommRingCat.ofHom φ))),
      ∃ (ψ : Ag →+* K) (g'' : XK ⟶ Xg)
        (_ : IsPullback g'' fK snd (Spec.map (CommRingCat.ofHom ψ))),
        g'' ≫ fst = gK ∧ ψ.comp α = φ := by
    intro K _ φ hφg XK fK gK hsq
    have hu : IsUnit (φ g) := isUnit_iff_ne_zero.2 hφg
    set ψ : Ag →+* K := IsLocalization.Away.lift g hu
    have hψ : ψ.comp α = φ := IsLocalization.Away.lift_comp g hu
    have hspec : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom α) =
        Spec.map (CommRingCat.ofHom φ) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    let g'' : XK ⟶ Xg := pullback.lift gK (fK ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [Category.assoc, hspec, hsq.w])
    have h1 : g'' ≫ fst = gK := pullback.lift_fst _ _ _
    have h2 : g'' ≫ snd = fK ≫ Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
    refine ⟨ψ, g'', IsPullback.of_right ?_ h2 hsqg, h1, hψ⟩
    rwa [h1, hspec]
  have hpt : ∀ {K : Type u} [Field K] (φ : A →+* K) (ψ : Ag →+* K) (_ : ψ.comp α = φ)
      (x : Spec (.of K)),
      PrimeSpectrum.comap α (Spec.map (CommRingCat.ofHom ψ) x) =
        ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ := by
    intro K _ φ ψ hψ x
    obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    ext1
    show Ideal.comap α (Ideal.comap ψ (IsLocalRing.maximalIdeal K)) = RingHom.ker φ
    rw [Ideal.comap_comap, hψ, IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  set W : Set Xg := ⋃ i, Stacks.Ample.nonvanishingLocus Fg (e i)
  have hW : IsOpen W := isOpen_iUnion fun i =>
    Stacks.NonvanishingOpen.isOpen_nonvanishingLocus Xg Fg (e i)
  set C : Set (Spec (.of Ag)) := snd '' Wᶜ
  have hC : IsClosed C := snd.isClosedMap _ hW.isClosed_compl
  have hemb := PrimeSpectrum.localization_away_isOpenEmbedding Ag g
  set U : Set (PrimeSpectrum A) := PrimeSpectrum.comap α '' Cᶜ
  have hU : IsOpen U := hemb.isOpenMap _ hC.isOpen_compl
  have hpU : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∈ U := by
    obtain ⟨K, _, φ, hφ, Xp, fp, gp, hsq, -, hgen⟩ := hp
    have hφg := map_ne_zero_of_ker_eq hφ hg
    obtain ⟨ψ, g'', hsq', hg'', hψ⟩ := hfib φ hφg hsq
    set x₀ : Spec (.of K) := IsLocalRing.closedPoint K
    refine ⟨Spec.map (CommRingCat.ofHom ψ) x₀, ?_, (hpt φ ψ hψ x₀).trans (by ext1; exact hφ)⟩
    rintro ⟨x, hxW, hx⟩
    obtain ⟨z₀, hz₀, hz₀'⟩ := Scheme.Pullback.exists_preimage_pullback x x₀ hx
    set z := hsq'.isoPullback.inv z₀
    have hz : g'' z = x := by
      rw [← hz₀, ← Scheme.Hom.comp_apply, hsq'.isoPullback_inv_fst]
    have := AlgebraicGeometry.SheafOfModules.isInvertible_pullback (g'' ≫ fst) F
    obtain ⟨σ⟩ : Nonempty ((Scheme.Modules.pullback (g'' ≫ fst)).obj F).GeneratingSections :=
      hg''.symm ▸ hgen
    obtain ⟨i₀, hi₀⟩ := exists_mem_nonvanishingLocus_of_generatingSections _ σ z
    obtain ⟨c, hc⟩ := hspan ψ hsq' (Stacks.NonvanishingSpelling.sectionsEquiv _ _ (σ.s i₀))
    rw [hc] at hi₀
    obtain ⟨i, -, hi⟩ := exists_mem_nonvanishingLocus_of_sum_smul _ Finset.univ c _ hi₀
    exact hxW (hz ▸ Set.mem_iUnion.2 ⟨i, (hbasis ψ hsq' i z).1 hi⟩)
  obtain ⟨_, ⟨g', rfl⟩, hpg', hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
  refine ⟨g', hpg', fun {K} _ φ hφg' XK fK gK hsq => ?_⟩
  obtain ⟨q'', hq''C, hq''⟩ := hsub (show
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum A) ∈
    PrimeSpectrum.basicOpen g' from fun h => hφg' (RingHom.mem_ker.1 h))
  have hφg : φ g ≠ 0 := by
    intro h
    have h' : α g ∈ q''.asIdeal := show g ∈ (PrimeSpectrum.comap α q'').asIdeal by
      rw [hq'']
      exact RingHom.mem_ker.2 h
    exact q''.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hα)
  obtain ⟨ψ, g'', hsq', hg'', hψ⟩ := hfib φ hφg hsq
  have := AlgebraicGeometry.SheafOfModules.isInvertible_pullback (g'' ≫ fst) F
  rw [← hg'']
  refine nonempty_generatingSections_of_forall_mem_nonvanishingLocus _
    (fun i => Φ (ψ.comp α) (hα.map ψ)
      (Stacks.Cech.isPullback_comp_specMap α ψ f snd fK fst g'' hsqg hsq') (Pi.single i 1))
    fun z => ?_
  have hz : g'' z ∈ W := by
    by_contra hz
    have hs : snd (g'' z) = q'' := hemb.injective (by
      rw [hq'', ← Scheme.Hom.comp_apply, hsq'.w, Scheme.Hom.comp_apply]
      exact hpt φ ψ hψ _)
    exact hq''C ⟨g'' z, hz, hs⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
  exact ⟨i, (hbasis ψ hsq' i z).2 hi⟩

end GlobalGeneration

end AlgebraicGeometry.C1590Private

end
