module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChainEnvelope07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUnitMono07QA
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechPackage07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerOpenData07Q9

/-!
# The module unit of an iterated `α_p`-cover is injective, over a chain normal form

For `f : X' ⟶ X` an iterated `α_p`-cover and `ℱ` a crystal in quasi-coherent modules on
`Cris(X/S)`, this file reduces the injectivity of `u_{X/S, *}(ℱ ⟶ f_{cris, *}f_cris^*ℱ)` — the
vanishing of `ℋ^{-1}` of the cone of the comparison map of [Stacks, Tag 07Q9], used by the
cokernel bound of [Stacks, Tag 07QA] — to the splitness of `D(0) ⟶ D'(0)` over the affine opens
with a chain normal form, the degree-zero shadow of the proof of [Stacks, Tag 07Q9].

Over such an open `W`, the Čech system `T(•)_e` of `W` (finite levels `D(0)/(p)^{N + e}`) and
the Čech system of `f⁻¹(W)` for the chain presentation (finite levels `D'(0)/(p)^{N' + e}`) are
related by `...SmallSite.chainCechSystemHom07Q9`.  A section of `ℱ` over `T(0)_{e + N'}` whose
image in `(f_cris^*ℱ)(T'(0)_e) = D'(0)/(p)^{N'+e} ⊗ ℱ(T(0)_{e + N'})` vanishes lies in
`(p)^{N' + e} ℱ(T(0)_{e + N'})`, by the retraction; at `e = N + l` it restricts to zero on
`T(0)_l`.  The sections over `W` inject into `lim_l ℱ(T(0)_l)`, and the affine opens with chain
normal forms form a basis.

## Main results

* `tauRing_openSystemMap07Q9_apply` — the morphism of Čech systems over `f`, read on rings, is
  the map of finite levels `D(n)/(p)^{N + e + N'} ⟶ D'(n)/(p)^{N' + e}`.
* `exists_retraction_of_level` — a retraction of `D ⟶ D'` gives a retraction of the finite level
  map modulo an ideal of `(p)^m`-classes.
* `forall_exists_restrict_eq_zero_openCechSystemHom07Q9` — the per-level hypothesis of
  `...SmallSite.mono_zariskiDirectImage_map_of_cechSystemHom`.
* `mono_zariskiDirectImage_map_crisModuleUnit_of_retraction` — the monomorphism, from the
  retractions of `D(0) ⟶ D'(0)` over the chain normal forms.
* `mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover` — **the monomorphism**,
  with the retractions `...SmallSite.chainEnvelopeRetraction07Q9`.

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.26.2, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  {X' : Scheme.{u}} (f : X' ⟶ S.X)
  (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {ι κ : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A
    →ₐ[(openAffineSituation07Q9 S hW hVW).A] (openAffineSituation07Q9 S hW hVW).C)
  (hg : Function.Surjective g)
  (g₂ : MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A
    →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A] (openAffineSituation₂07Q9 S hVW f hW₂).C)
  (hg₂ : Function.Surjective g₂)
  (r : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →+*
    MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A)
  (hrC : ∀ b, r (MvPolynomial.C b) = MvPolynomial.C b)
  (hr : g₂.toRingHom.comp r = (restrictMap07Q9 S hVW f).appTop.hom.comp g.toRingHom)

section QuotientRetraction

variable {D D' : Type*} [CommRing D] [CommRing D'] (φ : D →+* D') (ρ : D' →+ D)
  (hρ : ∀ a x, ρ (φ a * x) = a * ρ x)

include hρ in
/-- A retraction which is linear over `φ` carries `(p)^m D'` into `(p)^m D`. -/
theorem map_mem_span_pow_of_retraction (p m : ℕ) {x : D'}
    (hx : x ∈ Ideal.span {(p : D')} ^ m) : ρ x ∈ Ideal.span {(p : D)} ^ m := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨ρ y, ?_⟩
  rw [show y * (p : D') ^ m = φ ((p : D) ^ m) * y by rw [map_pow, map_natCast, mul_comm], hρ,
    mul_comm]

/-- **The retraction modulo `(p)^m`**: a retraction `ρ : D' → D` linear over `φ` induces an
additive map `D'/(p)^m ⟶ D/(p)^m`. -/
def quotientRetraction (p m : ℕ) :
    D' ⧸ Ideal.span {(p : D')} ^ m →+ D ⧸ Ideal.span {(p : D)} ^ m :=
  QuotientAddGroup.map (Ideal.span {(p : D')} ^ m).toAddSubgroup
    (Ideal.span {(p : D)} ^ m).toAddSubgroup ρ
    (fun _ hx => map_mem_span_pow_of_retraction φ ρ hρ p m hx)

/-- `quotientRetraction` on classes. -/
theorem quotientRetraction_mk (p m : ℕ) (x : D') :
    quotientRetraction φ ρ hρ p m (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ρ x) :=
  rfl

/-- The reduction `D/(p)^k ⟶ D/(p)^m` for `m ≤ k`. -/
def levelFactor (D : Type*) [CommRing D] (p : ℕ) {k m : ℕ} (h : m ≤ k) :
    D ⧸ Ideal.span {(p : D)} ^ k →+* D ⧸ Ideal.span {(p : D)} ^ m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right h)

/-- `levelFactor` on classes. -/
theorem levelFactor_mk (D : Type*) [CommRing D] (p : ℕ) {k m : ℕ} (h : m ≤ k) (x : D) :
    levelFactor D p h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x :=
  rfl

/-- `levelFactor` is surjective. -/
theorem levelFactor_surjective (D : Type*) [CommRing D] (p : ℕ) {k m : ℕ} (h : m ≤ k) :
    Function.Surjective (levelFactor D p h) :=
  Ideal.Quotient.factor_surjective _

/-- **A retraction onto a quotient becomes a retraction modulo the kernel.**  If `π : R → Q` is a
surjective ring map and `ρ' : R' → Q` is additive with `ρ'(τ a · t) = π a · ρ' t` and `ρ' 1 = 1`,
then `ρ'` read in `R/ker π ≅ Q` is a retraction of `τ` modulo `ker π`. -/
theorem exists_retraction_quotient_ker {R R' Q : Type*} [CommRing R] [CommRing R'] [CommRing Q]
    (τ : R →+* R') (π : R →+* Q) (hπ : Function.Surjective π) (ρ' : R' →+ Q)
    (hρ' : ∀ a t, ρ' (τ a * t) = π a * ρ' t) (h1 : ρ' 1 = 1) :
    ∃ r : R' →+ R ⧸ RingHom.ker π,
      (∀ a t, r (τ a * t) = Ideal.Quotient.mk _ a * r t) ∧ r 1 = 1 := by
  refine ⟨(RingHom.quotientKerEquivOfSurjective hπ).symm.toAddMonoidHom.comp ρ', fun a t => ?_,
    ?_⟩
  · change (RingHom.quotientKerEquivOfSurjective hπ).symm (ρ' (τ a * t)) =
      Ideal.Quotient.mk _ a * (RingHom.quotientKerEquivOfSurjective hπ).symm (ρ' t)
    rw [hρ', map_mul, RingHom.quotientKerEquivOfSurjective_symm_apply]
  · change (RingHom.quotientKerEquivOfSurjective hπ).symm (ρ' 1) = 1
    rw [h1, map_one]

include hρ in
/-- **The retraction modulo a level, transported along identifications of the rings.**  Let
`φ : D → D'` have a retraction `ρ` linear over `φ` with `ρ 1 = 1`, let `Γ ≃ D/(p)^k` and
`Γ' ≃ D'/(p)^m` with `m ≤ k`, and let `τ : Γ → Γ'` be the reduction of `φ` through these
identifications.  Then there is an ideal `J` of `Γ`, whose elements correspond to classes of
elements of `(p)^m`, and a retraction `Γ' → Γ/J` of `τ` modulo `J` sending `1` to `1`. -/
theorem exists_retraction_of_level {Γ Γ' : Type*} [CommRing Γ] [CommRing Γ'] (p k m : ℕ)
    (hmk : m ≤ k) (φA : Γ ≃+* D ⧸ Ideal.span {(p : D)} ^ k)
    (φA' : Γ' ≃+* D' ⧸ Ideal.span {(p : D')} ^ m) (τ : Γ →+* Γ')
    (hτ : ∀ d, φA' (τ (φA.symm (Ideal.Quotient.mk _ d))) = Ideal.Quotient.mk _ (φ d))
    (hρ1 : ρ 1 = 1) :
    ∃ (J : Ideal Γ) (rr : Γ' →+ Γ ⧸ J), (∀ a ∈ J, ∃ d ∈ Ideal.span {(p : D)} ^ m,
        φA a = Ideal.Quotient.mk _ d) ∧
      (∀ a t, rr (τ a * t) = Ideal.Quotient.mk _ a * rr t) ∧ rr 1 = 1 := by
  let π : Γ →+* D ⧸ Ideal.span {(p : D)} ^ m := (levelFactor D p hmk).comp φA.toRingHom
  have hπ : Function.Surjective π := (levelFactor_surjective D p hmk).comp φA.surjective
  let ρ' : Γ' →+ D ⧸ Ideal.span {(p : D)} ^ m :=
    (quotientRetraction φ ρ hρ p m).comp φA'.toAddMonoidHom
  have hρ' : ∀ a t, ρ' (τ a * t) = π a * ρ' t := by
    intro a t
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (φA a)
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φA' t)
    have ha : a = φA.symm (Ideal.Quotient.mk _ d) := by rw [hd, φA.symm_apply_apply]
    change quotientRetraction φ ρ hρ p m (φA' (τ a * t)) =
      levelFactor D p hmk (φA a) * quotientRetraction φ ρ hρ p m (φA' t)
    rw [map_mul φA', ha, hτ, φA.apply_symm_apply, ← hx, ← map_mul, quotientRetraction_mk,
      quotientRetraction_mk, hρ, levelFactor_mk, map_mul]
  obtain ⟨rr, hrr, hrr1⟩ := exists_retraction_quotient_ker τ π hπ ρ' hρ' (by
    change quotientRetraction φ ρ hρ p m (φA' 1) = 1
    rw [map_one, ← map_one (Ideal.Quotient.mk (Ideal.span {(p : D')} ^ m)),
      quotientRetraction_mk, hρ1, map_one])
  refine ⟨RingHom.ker π, rr, fun a ha => ?_, hrr, hrr1⟩
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (φA a)
  refine ⟨d, ?_, hd.symm⟩
  rwa [← Ideal.Quotient.eq_zero_iff_mem, ← levelFactor_mk D p hmk, hd]

end QuotientRetraction

/-- **The morphism of Čech systems over `f`, read on rings.** -/
theorem tauRing_openSystemMap07Q9_apply (n e : ℕ)
    (x : (levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂)).obj.ring) :
    haveI := isAffine_restrictX07Q9 S hW hVW
    haveI := isAffine_restrictS07Q9 S hV hVW
    tauRing (openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n e)
        (((wholeSiteEquivLittleAffine
          (isNilpotent_prime_openSituation07Q9 S hW hVW)).counitIso.inv.app
          (levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂))).hom.hom x) =
      (levelCounit₂07Q9 S hV hVW f hW₂ g₂ hg₂ n e).hom
        (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n e x) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  exact congrArg (fun φ => φ.hom x)
    (levelBridge_localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hrC hr n e)

/-- **The per-level hypothesis of `mono_zariskiDirectImage_map_of_cechSystemHom` for the morphism
of Čech systems attached to a morphism of presentations**, given a `D(0)`-linear retraction of
`D(0) ⟶ D'(0)`.  For every level `l`, at the level `e = N + l`, a section of `ℱ` over
`T(0)_{e + N'}` killed by the module unit followed by the evaluation at `τ_e` restricts to zero on
`T(0)_l`. -/
theorem forall_exists_restrict_eq_zero_openCechSystemHom07Q9
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F)
    (ρ : (tensorPowerEnvelopeThickening _ g₂ hg₂ 0).thickening.ring →+
      (tensorPowerEnvelopeThickening _ g hg 0).thickening.ring)
    (hρ : ∀ a x, ρ ((envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr 0).toRingHom a * x) =
      a * ρ x) (hρ1 : ρ 1 = 1) (l : ℕ) :
    ∃ (e : ℕ) (hle : l ≤ e + (openCechSystemHom07Q9 S hV hW hVW g hg f hW₂ g₂ hg₂ r hrC hr).k),
      ∀ y : ((toAbelianSheaf S).obj ((moduleULift S).obj F)).obj.obj
          (op (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).obj
            (e + (openCechSystemHom07Q9 S hV hW hVW g hg f hW₂ g₂ hg₂ r hrC hr).k))),
        ((crisModuleUnit (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)
            ((moduleULift S).obj F)).hom.app
            (op (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).obj
              (e + (openCechSystemHom07Q9 S hV hW hVW g hg f hW₂ g₂ hg₂ r hrC hr).k))) ≫
          crisDirectImageEval (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)
            ((openCechSystemHom07Q9 S hV hW hVW g hg f hW₂ g₂ hg₂ r hrC hr).τ ⦋0⦌ e)
            ((toAbelianSheaf (overSituation S f)).obj
              ((crisModuleInverseImage (S := overSituation S f) (S' := S) (𝟙 S.S) f
                (overSituation_compat S f)).obj
                ((moduleULift S).obj F)))) y = 0 →
        ((toAbelianSheaf S).obj ((moduleULift S).obj F)).obj.map
          (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).map (homOfLE hle)).op y = 0 := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  have := isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)
  have := isAffine_restrictS07Q9 (overSituation S f) hV (preimage_le_overSituation07Q9 S hVW f)
  set N := uniformLevel (openAffineSituation07Q9 S hW hVW)
  set N' := openSystemShift07Q9 S hVW f hW₂
  have hle' : l ≤ N + l + N' := by omega
  refine ⟨N + l, hle', fun y hy => ?_⟩
  have := isAffine_target_openSystem07Q9 S hV hW hVW g hg 0 (N + l + N')
  have := isAffine_target_openSystem07Q9 (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂ 0 (N + l)
  let D := (tensorPowerEnvelopeThickening _ g hg 0).thickening.ring
  let D' := (tensorPowerEnvelopeThickening _ g₂ hg₂ 0).thickening.ring
  let pp := (openAffineSituation07Q9 S hW hVW).p
  let φA : ((crisCommRing S).obj (op ((CrystallineThickening.ι S).obj
      (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).obj (N + l + N')))) : Type u) ≃+*
      (D ⧸ Ideal.span {(pp : D)} ^ (N + (N + l + N'))) :=
    wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (levelObj07Q9 S hW hVW g hg 0 (N + l + N'))
  let φA' : Γ(((changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).obj
      ((CrystallineThickening.ι (overSituation S f)).obj
        (((openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
          g₂ hg₂).obj (op ⦋0⦌)).obj (N + l)))).thickening.target.scheme, ⊤) ≃+*
      (D' ⧸ Ideal.span {(pp : D')} ^ (N' + (N + l))) :=
    wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9
      (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f))
      (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ 0 (N + l))
  have hτ : ∀ d, φA' ((tauRing (openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hrC hr 0
      (N + l))).hom (φA.symm (Ideal.Quotient.mk _ d))) =
      Ideal.Quotient.mk _
        ((envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr 0).toRingHom d) :=
    fun d => (congrArg φA' (tauRing_openSystemMap07Q9_apply S hV hW hVW f hW₂ g hg g₂ hg₂ r hrC hr
      0 (N + l) (Ideal.Quotient.mk _ d))).trans (φA'.apply_symm_apply _)
  obtain ⟨J, rr, hJ, hrr, hrr1⟩ := exists_retraction_of_level
    (envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hrC hr 0).toRingHom ρ hρ
    pp (N + (N + l + N')) (N' + (N + l)) (by omega) φA φA'
    (tauRing (openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hrC hr 0 (N + l))).hom hτ hρ1
  have hJ' : ∀ a ∈ J, (crisCommRing S).map ((CrystallineThickening.ι S).map
      (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).map (homOfLE hle'))).op a = 0 := by
    intro a ha
    obtain ⟨d, hd, hda⟩ := hJ a ha
    let φB : ((crisCommRing S).obj (op ((CrystallineThickening.ι S).obj
        (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).obj l))) : Type u) ≃+*
        (D ⧸ Ideal.span {(pp : D)} ^ (N + l)) :=
      wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (levelObj07Q9 S hW hVW g hg 0 l)
    refine φB.injective ?_
    have hnat := wholeSiteInverseSectionsRingEquiv_naturality
      (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (((affineLevelSystem _ g hg).obj ⦋0⦌).map
        ((homOfLE hle').op : (op (N + l + N') : ℕᵒᵖ) ⟶ op l)) a
    refine hnat.trans ?_
    rw [map_zero]
    change (((affineLevelSystem _ g hg).obj ⦋0⦌).map
        ((homOfLE hle').op : (op (N + l + N') : ℕᵒᵖ) ⟶ op l)).hom.hom.toRingHom (φA a) = 0
    rw [hda]
    change (Ideal.Quotient.mk (Ideal.span {(pp : D)} ^ (N + l)) d :
      D ⧸ Ideal.span {(pp : D)} ^ (N + l)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right (by omega) hd
  have := isAffine_target_openSystem07Q9 S hV hW hVW g hg 0
    (N + l + (openCechSystemHom07Q9 S hV hW hVW g hg f hW₂ g₂ hg₂ r hrC hr).k)
  exact restrict_eq_zero_of_crisModuleUnit_eval_eq_zero (S := overSituation S f) (S' := S)
    (𝟙 S.S) f (overSituation_compat S f) F
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF.1) hF.2 _
    ((openCechSystemHom07Q9 S hV hW hVW g hg f hW₂ g₂ hg₂ r hrC hr).τ ⦋0⦌ (N + l)) J hJ' rr
    hrr hrr1 y hy

section Assembly

variable (T : GlobalCrystallineSituation.{u}) {X' : Scheme.{u}} (f : X' ⟶ T.X)

/-- **`u_{X/S, *}` of the module unit of an iterated `α_p`-cover is a monomorphism, given the
retractions of the envelopes.**  For `f : X' ⟶ X` an iterated `α_p`-cover and `ℱ` a crystal in
quasi-coherent modules, `u_{X/S, *}(ℱ ⟶ f_{cris, *}f_cris^*ℱ)` is a monomorphism as soon as, over
every affine open `W` with affine preimage and a chain normal form, the map `D(0) ⟶ D'(0)` of
completed envelopes of the canonical presentation of `Γ(W)` and of the chain presentation of
`Γ(f⁻¹(W))` has a `D(0)`-linear retraction sending `1` to `1`. -/
theorem mono_zariskiDirectImage_map_crisModuleUnit_of_retraction
    (hf : IsIteratedAlphaPCover T.p f) (F : SheafOfModules.{u} (structureSheaf T))
    (hF : IsQuasiCoherentCrystal T F)
    (hρ : ∀ {V : T.S.scheme.Opens} {W : T.X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
      (hVW : W ≤ sourceToBase T ⁻¹ᵁ V) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {n : ℕ}
      (ch : AlphaPChain T.p Γ(T.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)
      (he : f.app W ≫ e.hom = ch.toTop),
      ∃ ρ : (tensorPowerEnvelopeThickening _ (chainPresentation07Q9 T hW hVW f hW₂ ch e)
          (surjective_chainPresentation07Q9 T hW hVW f hW₂ ch e he) 0).thickening.ring →+
          (tensorPowerEnvelopeThickening _
            (canonicalPresentation (openAffineSituation07Q9 T hW hVW))
            (canonicalPresentation_surjective _) 0).thickening.ring,
        (∀ a x, ρ ((envelopeRingMap07Q9 T hW hVW f hW₂ _ (canonicalPresentation_surjective _) _
          (surjective_chainPresentation07Q9 T hW hVW f hW₂ ch e he)
          (chainPresentationRename07Q9 T hW hVW f hW₂)
          (chainPresentationRename07Q9_C T hW hVW f hW₂)
          (chainPresentation07Q9_comp_rename T hW hVW f hW₂ ch e) 0).toRingHom a * x) = a * ρ x) ∧
        ρ 1 = 1) :
    Mono ((zariskiDirectImage T).map (crisModuleUnit (overSituation T f) T (𝟙 T.S) f
      (overSituation_compat T f) ((moduleULift T).obj F))) := by
  refine mono_zariskiDirectImage_map_of_cechSystemHom _
    (ℬ := {W | ∃ V : T.S.scheme.Opens, IsAffineOpen V ∧ ∃ (hW : IsAffineOpen W)
      (hVW : W ≤ sourceToBase T ⁻¹ᵁ V), IsAffineOpen (f ⁻¹ᵁ W) ∧
        ∃ (n : ℕ) (ch : AlphaPChain T.p Γ(T.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top),
          f.app W ≫ e.hom = ch.toTop}) ?_ ?_
  · refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {N x} hx => ?_
    obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      T.S.scheme.isBasis_affineOpens (show (sourceToBase T) x ∈ (⊤ : T.S.scheme.Opens) from trivial)
    obtain ⟨W, hW, hW₂, hxW, hWN, n, ch, e, he⟩ := exists_isAffineOpen_alphaPChain hf
      (N := N ⊓ sourceToBase T ⁻¹ᵁ V) ⟨hx, hxV⟩
    exact ⟨W, ⟨V, hV, hW, hWN.trans inf_le_right, hW₂, n, ch, e, he⟩, hxW, hWN.trans inf_le_left⟩
  · rintro W ⟨V, hV, hW, hVW, hW₂, n, ch, e, he⟩
    obtain ⟨ρ, hρm, hρ1⟩ := hρ hV hW hVW hW₂ ch e he
    exact ⟨_, _,
      isOpenProCovering_openSystem07Q9 T hV hW hVW _ (canonicalPresentation_surjective _),
      chainCechSystemHom07Q9 T hV hW hVW f hW₂ ch e he,
      forall_exists_restrict_eq_zero_openCechSystemHom07Q9 T hV hW hVW f hW₂ _
        (canonicalPresentation_surjective _) _
        (surjective_chainPresentation07Q9 T hW hVW f hW₂ ch e he)
        (chainPresentationRename07Q9 T hW hVW f hW₂) (chainPresentationRename07Q9_C T hW hVW f hW₂)
        (chainPresentation07Q9_comp_rename T hW hVW f hW₂ ch e) F hF ρ hρm hρ1⟩

/-- **`u_{X/S, *}` of the module unit of an iterated `α_p`-cover is a monomorphism.**  For
`f : X' ⟶ X` an iterated `α_p`-cover and `ℱ` a crystal in quasi-coherent modules on `Cris(X/S)`,
the map `u_{X/S, *}ℱ ⟶ u_{X/S, *}f_{cris, *}f_cris^*ℱ` is injective.  Equivalently
(`...SmallSite.mono_homologyMap_moduleComparison07Q9_iff`), the cone of the comparison map of
[Stacks, Tag 07Q9] has no cohomology sheaf in degree `-1`.  The retractions of `D(0) ⟶ D'(0)` over
the chain normal forms are `...SmallSite.chainEnvelopeRetraction07Q9`. -/
theorem mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover
    (hf : IsIteratedAlphaPCover T.p f) (F : SheafOfModules.{u} (structureSheaf T))
    (hF : IsQuasiCoherentCrystal T F) :
    Mono ((zariskiDirectImage T).map (crisModuleUnit (overSituation T f) T (𝟙 T.S) f
      (overSituation_compat T f) ((moduleULift T).obj F))) :=
  mono_zariskiDirectImage_map_crisModuleUnit_of_retraction T f hf F hF
    fun _ hW hVW hW₂ _ ch e he => ⟨chainEnvelopeRetraction07Q9 T hW hVW f hW₂ ch e he rfl,
      chainEnvelopeRetraction07Q9_mul_left T hW hVW f hW₂ ch e he rfl,
      chainEnvelopeRetraction07Q9_one T hW hVW f hW₂ ch e he rfl⟩

end Assembly

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
