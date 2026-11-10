module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection.FinsumIntersections

/-!
# Coefficients of intersection cycles

The coefficient of an intersection cycle at a point of `D` as a colength in the local ring of
`X`, with the localization and nonzerodivisor lemmas it rests on.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open TopologicalSpace

open scoped TensorProduct

universe v w

open CategoryTheory.Limits Opposite

attribute [local instance] Classical.propDecidable

/-- The point of `Spec 𝒪_{X,z}` indexed by `q` maps to the point of an affine open `U ∋ z`
given by the contraction of `q` along the germ map. -/
private lemma fromSpecStalk_eq_fromSpec_comap {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (q : PrimeSpectrum (X.presheaf.stalk z)) :
    X.fromSpecStalk z q = hU.fromSpec (PrimeSpectrum.comap (X.presheaf.germ U z hz).hom q) := by
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hz]
  rfl

/-- A point of a closed subscheme maps into the support of its ideal sheaf. -/
private lemma subschemeι_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) (w : I.subscheme) :
    I.subschemeι w ∈ (I.support : Set X) :=
  I.range_subschemeι ▸ Set.mem_range_self w

/-- A point of the support of an ideal sheaf lifts to its closed subscheme. -/
private lemma exists_subschemeι_eq_of_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) {y : X}
    (hy : y ∈ (I.support : Set X)) : ∃ w : I.subscheme, I.subschemeι w = y := by
  rwa [← I.range_subschemeι] at hy

/-- A point of `Z ∩ D`, viewed in `X` through `D`, lies in the support of `Z`. -/
private lemma subschemeι_comap_mem_support {X : Scheme.{u}} (Z D : X.IdealSheafData)
    (w : (Z.comap D.subschemeι).subscheme) :
    D.subschemeι ((Z.comap D.subschemeι).subschemeι w) ∈ (Z.support : Set X) := by
  have h := subschemeι_mem_support (Z.comap D.subschemeι) w
  rwa [Scheme.IdealSheafData.support_comap] at h

/-- A point whose closure is an irreducible component has no proper generization. -/
private lemma eq_of_specializes_of_closure_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] [T0Space T] {x v : T}
    (hx : closure ({x} : Set T) ∈ irreducibleComponents T) (h : v ⤳ x) : v = x := by
  have hsub : closure ({x} : Set T) ⊆ closure ({v} : Set T) := h.closure_subset
  have hgen : IsGenericPoint v (closure ({x} : Set T)) :=
    Set.Subset.antisymm (hx.2 isIrreducible_singleton.closure hsub) hsub
  exact hgen.eq isGenericPoint_closure

/-- The closure of a point with no proper generization is an irreducible component. -/
private lemma closure_mem_irreducibleComponents_of_specializes_eq {T : Type*}
    [TopologicalSpace T] [QuasiSober T] {x : T} (h : ∀ v : T, v ⤳ x → v = x) :
    closure ({x} : Set T) ∈ irreducibleComponents T := by
  refine ⟨isIrreducible_singleton.closure, fun V hV hsub => ?_⟩
  have hgen : IsGenericPoint hV.genericPoint (closure V) :=
    hV.isGenericPoint_genericPoint_closure
  have hspec : hV.genericPoint ⤳ x :=
    specializes_iff_mem_closure.mpr (hgen ▸ subset_closure (hsub (subset_closure rfl)))
  intro v hv
  rw [← h _ hspec, hgen]
  exact subset_closure hv

/- The stalk at `z` of the reduced structure on the closure of a point `y`
specialising to `z` is exactly the prime of the local ring at `z` that `y`
corresponds to under `Scheme.fromSpecStalk`. The closed-point case is the
statement that the stalk of the vanishing ideal of `closure {z}` is the maximal
ideal. -/
private theorem stalk_reducedPointClosure_fromSpecStalk {X : Scheme.{u}} (z : X)
    (q : PrimeSpectrum (X.presheaf.stalk z)) :
    IdealSheafData.stalk
      (reducedPointClosure (X.fromSpecStalk z q)) z = q.asIdeal := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let Ua : X.affineOpens := ⟨U, hU⟩
  have hAff : IsAffineOpen U := hU
  let : IsOpenImmersion hAff.fromSpec := hAff.isOpenImmersion_fromSpec
  let p := hAff.primeIdealOf ⟨z, hzU⟩
  let g := X.presheaf.germ U z hzU
  let p' : PrimeSpectrum Γ(X, U) := PrimeSpectrum.comap g.hom q
  have hy : X.fromSpecStalk z q = hAff.fromSpec p' :=
    fromSpecStalk_eq_fromSpec_comap hAff z hzU q
  have hpre : (hAff.fromSpec : AlgebraicGeometry.Spec (.of Γ(X, U)) ⟶ X) ⁻¹'
      ({X.fromSpecStalk z q} : Set X) = ({p'} : Set (PrimeSpectrum Γ(X, U))) := by
    ext w
    change hAff.fromSpec w = X.fromSpecStalk z q ↔ w = p'
    rw [hy]
    exact ⟨fun hw => hAff.fromSpec.isOpenEmbedding.injective hw, fun hw => by rw [hw]⟩
  have hcl : (hAff.fromSpec : AlgebraicGeometry.Spec (.of Γ(X, U)) ⟶ X) ⁻¹'
      closure ({X.fromSpecStalk z q} : Set X) =
        closure ({p'} : Set (PrimeSpectrum Γ(X, U))) := by
    rw [hAff.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hAff.fromSpec.continuous, hpre]
    rfl
  have hvi := congrArg PrimeSpectrum.vanishingIdeal hcl
  rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton] at hvi
  have hideal : (reducedPointClosure (X.fromSpecStalk z q)).ideal Ua = p'.asIdeal := by
    rw [reducedPointClosure, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact hvi
  let : Algebra Γ(X, U) (X.presheaf.stalk z) := g.hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk z) p.asIdeal :=
    hAff.isLocalization_stalk ⟨z, hzU⟩
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ z Ua hzU, hideal]
  exact IsLocalization.map_under p.asIdeal.primeCompl (X.presheaf.stalk z) q.asIdeal

/- An effective Cartier divisor on a closed subscheme contains no irreducible
component of that subscheme: at a generic point the local ring of the subscheme
has dimension zero, while an effective Cartier divisor through it would force
dimension one. -/
lemma genericPoint_not_mem_support_of_effectiveCartier_comap
    {X : Scheme.{u}} (Z D : X.IdealSheafData) [IsLocallyNoetherian Z.subscheme]
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap Z.subschemeι))
    (ξ : genericPoints Z.subscheme) :
    Z.subschemeι ξ.1 ∉ (D.support : Set X) := by
  intro hmem
  have hξcomp : closure ({ξ.1} : Set Z.subscheme) ∈
      irreducibleComponents Z.subscheme := ξ.2
  let E : Z.subscheme.IdealSheafData := D.comap Z.subschemeι
  have hξE : ξ.1 ∈ (E.support : Set Z.subscheme) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hmem
  rw [← E.range_subschemeι] at hξE
  obtain ⟨η, hη⟩ := hξE
  have hcompE : closure ({η} : Set E.subscheme) ∈ irreducibleComponents E.subscheme :=
    closure_mem_irreducibleComponents_of_specializes_eq fun ν hν => by
      have h := hν.map E.subschemeι.continuous
      rw [hη] at h
      exact E.subschemeι.isEmbedding.injective
        (by rw [hη]; exact eq_of_specializes_of_closure_mem_irreducibleComponents hξcomp h)
  have hdim1 := AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor
    (X := Z.subscheme) E hDZ η
    ⟨⟨closure ({η} : Set E.subscheme), hcompE⟩, isGenericPoint_closure⟩
  rw [hη] at hdim1
  have hmax : IsMax ξ.1 := fun y hy =>
    (eq_of_specializes_of_closure_mem_irreducibleComponents hξcomp hy).le
  have hzero : ringKrullDim (Z.subscheme.presheaf.stalk ξ.1) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast Order.coheight_eq_zero.mpr hmax
  rw [hzero] at hdim1
  exact absurd hdim1 (by simp)


attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Length is invariant along a ring isomorphism together with a compatible additive
isomorphism of modules. -/
private lemma length_eq_of_ringEquiv_semilinear
    {R S : Type*} [CommRing R] [CommRing S] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : R ≃+* S) (g : M ≃+ N)
    (hg : ∀ (r : R) (m : M), g (r • m) = e r • g m) :
    Module.length R M = Module.length S N := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let el : M ≃ₛₗ[(e : R →+* S)] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := hg,
      invFun := g.symm, left_inv := g.symm_apply_apply, right_inv := g.apply_symm_apply }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap el)]

/-- Clearing denominators: if `t * s₀ = r` in `A`, then `r • w = s₀ • t • w`. -/
private lemma smul_eq_smul_smul_of_mul_eq {R A N : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    {t : A} {r s₀ : R} (h : t * algebraMap R A s₀ = algebraMap R A r) (w : N) :
    r • w = s₀ • t • w := by
  rw [← IsScalarTower.algebraMap_smul A r w, ← h, mul_smul, IsScalarTower.algebraMap_smul]
  exact smul_comm _ _ _

/-- Composing two localization maps localizes at the contracted submonoid. -/
private lemma isLocalizedModule_comp
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    {M N P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    (S : Submonoid R) [IsLocalization S A] (T : Submonoid A)
    (hST : S ≤ T.comap (algebraMap R A))
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (g : N →ₗ[A] P) [IsLocalizedModule T g] :
    IsLocalizedModule (T.comap (algebraMap R A)) ((g.restrictScalars R).comp f) := by
  have hsurj : ∀ t : T, ∃ (r : R) (s₀ : S), (t : A) * algebraMap R A s₀ = algebraMap R A r ∧
      algebraMap R A r ∈ T := fun t => by
    obtain ⟨⟨r, s₀⟩, hrs⟩ := IsLocalization.surj S (t : A)
    exact ⟨r, s₀, hrs, hrs ▸ mul_mem t.2 (hST s₀.2)⟩
  constructor
  · intro s
    have h := IsLocalizedModule.map_units g ⟨algebraMap R A s.1, s.2⟩
    rw [Module.End.isUnit_iff] at h ⊢
    have key : (((algebraMap R (Module.End R P)) (s : R) : Module.End R P) : P → P) =
        (((algebraMap A (Module.End A P)) (algebraMap R A (s : R)) : Module.End A P) : P → P) :=
      funext fun x => by
        simp only [Module.algebraMap_end_apply, IsScalarTower.algebraMap_smul]
    rw [key]
    exact h
  · intro p
    obtain ⟨⟨n, t⟩, hnt⟩ := IsLocalizedModule.surj T g p
    have hnt' : (t : A) • p = g n := hnt
    obtain ⟨r, s₀, hrs, hrT⟩ := hsurj t
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj S f n
    have hms' : (s : R) • n = f m := hms
    refine ⟨⟨(s₀ : R) • m, ⟨(s : R) * r, mul_mem (hST s.2) hrT⟩⟩, ?_⟩
    change ((s : R) * r) • p = g (f ((s₀ : R) • m))
    have hg : ∀ (c : R) (w : N), g (c • w) = c • g w := fun c w =>
      LinearMap.map_smul_of_tower g c w
    rw [mul_smul, smul_eq_smul_smul_of_mul_eq hrs p, hnt', map_smul, hg, ← hms', hg]
    exact smul_comm _ _ _
  · intro m₁ m₂ h
    have h' : g (f m₁) = g (f m₂) := h
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) h'
    have ht' : (t : A) • f m₁ = (t : A) • f m₂ := ht
    obtain ⟨r, s₀, hrs, hrT⟩ := hsurj t
    have hr : f (r • m₁) = f (r • m₂) := by
      rw [map_smul, map_smul, smul_eq_smul_smul_of_mul_eq hrs, smul_eq_smul_smul_of_mul_eq hrs,
        ht']
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) hr
    have hc' : (c : R) • (r • m₁) = (c : R) • (r • m₂) := hc
    exact ⟨⟨(c : R) * r, mul_mem (hST c.2) hrT⟩, by
      simpa only [Submonoid.smul_def, mul_smul] using hc'⟩

/-- The length of a module localized at a prime of a localization, compared with the
length over the corresponding localization of the base ring. -/
lemma length_eq_of_localized_at_prime
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {A : Type*} [CommRing A] [Algebra R A] (S : Submonoid R) [IsLocalization S A]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (q : Ideal A) [hq : q.IsPrime]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalization q.primeCompl B]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module A Q] [Module B Q]
    [IsScalarTower R A Q] [IsScalarTower R B Q]
    (g : N →ₗ[A] Q) [IsLocalizedModule q.primeCompl g]
    {A' : Type*} [CommRing A'] [Algebra R A'] (T : Submonoid R)
    (hT : T = q.primeCompl.comap (algebraMap R A)) [IsLocalization T A']
    {N' : Type*} [AddCommGroup N'] [Module R N'] [Module A' N'] [IsScalarTower R A' N']
    (f' : M →ₗ[R] N') [IsLocalizedModule T f'] :
    Module.length A' N' = Module.length B Q := by
  subst hT
  have hpprime : (q.comap (algebraMap R A)).IsPrime := hq.comap _
  have hST : S ≤ q.primeCompl.comap (algebraMap R A) := by
    intro s hs hmem
    exact hq.ne_top (q.eq_top_of_isUnit_mem hmem (IsLocalization.map_units A ⟨s, hs⟩))
  have hcomp : IsLocalizedModule (q.primeCompl.comap (algebraMap R A))
      ((g.restrictScalars R).comp f) := isLocalizedModule_comp S q.primeCompl hST f g
  have _ : IsLocalization (q.primeCompl.comap (algebraMap R A)) B :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S B q
  let φ := IsLocalizedModule.linearEquiv (q.primeCompl.comap (algebraMap R A)) f'
    ((g.restrictScalars R).comp f)
  let ea := IsLocalization.algEquiv (q.primeCompl.comap (algebraMap R A)) A' B
  have hinj : ∀ s : (q.primeCompl.comap (algebraMap R A)),
      Function.Injective fun x : Q => (s : R) • x := by
    intro s
    have h := IsLocalizedModule.map_units ((g.restrictScalars R).comp f) s
    rw [Module.End.isUnit_iff] at h
    intro x y hxy
    exact h.1 (by simpa only [Module.algebraMap_end_apply] using hxy)
  have hcompat : ∀ (a : A') (n : N'), φ (a • n) = ea a • φ n := by
    intro a n
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (q.primeCompl.comap (algebraMap R A)) a
    have hrs' : a * algebraMap R A' (s : R) = algebraMap R A' r := hrs
    have h1 : (s : R) • (a • n) = (r : R) • n := by
      rw [← IsScalarTower.algebraMap_smul A' (s : R) (a • n), smul_smul, mul_comm, hrs',
        IsScalarTower.algebraMap_smul]
    have hea := congrArg ea hrs'
    rw [map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at hea
    have h2 : (s : R) • (ea a • φ n) = (r : R) • φ n := by
      rw [← IsScalarTower.algebraMap_smul B (s : R) (ea a • φ n), smul_smul, mul_comm, hea,
        IsScalarTower.algebraMap_smul]
    refine hinj s ?_
    change (s : R) • φ (a • n) = (s : R) • (ea a • φ n)
    rw [h2, ← map_smul, h1, map_smul]
  exact length_eq_of_ringEquiv_semilinear ea.toRingEquiv φ.toAddEquiv hcompat

/-- The prime of an affine open corresponding to a point of `Spec 𝒪_{X,z}` lying in it is the
contraction of that prime along the germ map. -/
lemma primeIdealOf_fromSpecStalk {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (z : X) (hz : z ∈ U) (q : PrimeSpectrum (X.presheaf.stalk z))
    (hy : X.fromSpecStalk z q ∈ U) :
    (hU.primeIdealOf ⟨X.fromSpecStalk z q, hy⟩).asIdeal =
      Ideal.comap (X.presheaf.germ U z hz).hom q.asIdeal := by
  let : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let p' : PrimeSpectrum Γ(X, U) := PrimeSpectrum.comap (X.presheaf.germ U z hz).hom q
  have hyy : X.fromSpecStalk z q = hU.fromSpec p' :=
    fromSpecStalk_eq_fromSpec_comap hU z hz q
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨X.fromSpecStalk z q, hy⟩) = X.fromSpecStalk z q :=
    hU.fromSpec_primeIdealOf ⟨X.fromSpecStalk z q, hy⟩
  exact congrArg PrimeSpectrum.asIdeal
    (hU.fromSpec.isOpenEmbedding.injective (h2.trans hyy))

/-- `Scheme.fromSpecStalk` is injective, being a preimmersion. -/
lemma fromSpecStalk_injective {X : Scheme.{u}} (z : X) :
    Function.Injective (X.fromSpecStalk z) :=
  (X.fromSpecStalk z).isEmbedding.injective

/-- The support of the reduced structure on the closure of a point is that closure. -/
lemma reducedPointClosure_support {X : Scheme.{u}} (y : X) :
    ((reducedPointClosure y).support : Set X) = closure ({y} : Set X) := by
  simp [reducedPointClosure]

/-- A point `x` of a closed subscheme `D` of relative dimension `k`, lying in the
closure of a point `y` of relative dimension `k + 1` that avoids `D`, is the image
of a generic point of an irreducible component of the intersection of `D` with the
reduced closure of `y`. This is the hypothesis under which the intersection cycle
has the expected coefficient at `x`. -/
lemma exists_genericPoint_comap_reducedPointClosure
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (D : X.IdealSheafData) (x : D.subscheme) (y : X)
    (hyz : y ⤳ D.subschemeι x) (hyD : y ∉ (D.support : Set X))
    (hy : relativeDimension C.dimensionFunction p y = k + 1)
    (hx : relativeDimension C.dimensionFunction (D.subschemeι ≫ p) x = k) :
    ∃ ξ : genericPoints ((reducedPointClosure y).comap D.subschemeι).subscheme,
      ((reducedPointClosure y).comap D.subschemeι).subschemeι ξ.1 = x := by
  classical
  have hxE : x ∈ Set.range ((reducedPointClosure y).comap D.subschemeι).subschemeι := by
    have h : D.subschemeι x ∈ ((reducedPointClosure y).support : Set X) := by
      rw [reducedPointClosure_support]
      exact hyz.mem_closure
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    exact h
  obtain ⟨η, hη⟩ := hxE
  have hEdim : ∀ w : ((reducedPointClosure y).comap D.subschemeι).subscheme,
      relativeDimension C.dimensionFunction (D.subschemeι ≫ p)
        (((reducedPointClosure y).comap D.subschemeι).subschemeι w) ≤ k := by
    intro w
    have hspec : y ⤳ D.subschemeι
        (((reducedPointClosure y).comap D.subschemeι).subschemeι w) :=
      specializes_iff_mem_closure.mpr (by
        rw [← reducedPointClosure_support]
        exact subschemeι_comap_mem_support _ _ w)
    have hne : y ≠ D.subschemeι
        (((reducedPointClosure y).comap D.subschemeι).subschemeι w) := by
      intro he
      refine hyD ?_
      rw [← D.range_subschemeι, he]
      exact ⟨((reducedPointClosure y).comap D.subschemeι).subschemeι w, rfl⟩
    have hlt := relativeDimension_lt_of_specializes C p hspec hne
    rw [hy] at hlt
    rw [relativeDimension_comp_closedImmersion C.dimensionFunction D.subschemeι p]
    omega
  have hcomp : closure ({η} :
      Set ((reducedPointClosure y).comap D.subschemeι).subscheme) ∈
      irreducibleComponents ((reducedPointClosure y).comap D.subschemeι).subscheme :=
    closure_mem_irreducibleComponents_of_specializes_eq fun ν hν => by
      have hmapspec : ((reducedPointClosure y).comap D.subschemeι).subschemeι ν ⤳ x :=
        hη ▸ hν.map ((reducedPointClosure y).comap D.subschemeι).subschemeι.continuous
      refine ((reducedPointClosure y).comap D.subschemeι).subschemeι.isEmbedding.injective ?_
      rw [hη]
      by_contra hne
      have hlt := relativeDimension_lt_of_specializes C (D.subschemeι ≫ p) hmapspec hne
      have hle := hEdim ν
      rw [hx] at hlt
      omega
  exact ⟨⟨η, hcomp⟩, hη⟩

/- The coefficient of the cycle of the inverse image of the reduced closure of a
point `y` specialising to `f x`: it is the colength in the local ring at `x` of
the ideal generated by the prime that `y` corresponds to. -/
private theorem closedSubschemeCycleCoeff_reducedPointClosure_comap_eq_length
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X ⟶ Y)
    (k : ℤ) (x : X) (q : PrimeSpectrum (Y.presheaf.stalk (f x)))
    (hgeneric : ∃ ξ : genericPoints
      ((reducedPointClosure (Y.fromSpecStalk (f x) q)).comap f).subscheme,
      ((reducedPointClosure (Y.fromSpecStalk (f x) q)).comap f).subschemeι ξ.1 = x)
    (hdim : relativeDimension C.dimensionFunction sX x = k) :
    closedSubschemeCycleCoeff C sX
      ((reducedPointClosure (Y.fromSpecStalk (f x) q)).comap f).subschemeι k x =
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸
          Ideal.map (f.stalkMap x).hom q.asIdeal)).toNat : ℤ) := by
  classical
  have key : ∀ ξ : genericPoints
      ((reducedPointClosure (Y.fromSpecStalk (f x) q)).comap f).subscheme,
      ((reducedPointClosure (Y.fromSpecStalk (f x) q)).comap f).subschemeι ξ.1 = x →
      componentMultiplicity
          ((reducedPointClosure (Y.fromSpecStalk (f x) q)).comap f).subschemeι ξ =
        ((Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸
            Ideal.map (f.stalkMap x).hom q.asIdeal)).toNat : ℤ) := by
    intro ξ hξ
    rw [componentMultiplicity_comap_eq_length_quotient f, hξ,
      stalk_reducedPointClosure_fromSpecStalk]
  unfold closedSubschemeCycleCoeff
  split_ifs with h
  · exact key (Classical.choose h) (Classical.choose_spec h).1
  · exact False.elim (h ⟨Classical.choose hgeneric,
      Classical.choose_spec hgeneric, hdim⟩)

/-- The same coefficient, rewritten as a colength in the local ring of the
ambient scheme: this is the shape in which Stacks 02QG states additivity. -/
theorem intersectionCycleCoeff_eq_length_quotient_sup
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (D : X.IdealSheafData) (k : ℤ) (x : D.subscheme)
    (a : X.presheaf.stalk (D.subschemeι x))
    (hker : RingHom.ker (D.subschemeι.stalkMap x).hom = Ideal.span {a})
    (q : PrimeSpectrum (X.presheaf.stalk (D.subschemeι x)))
    (hgeneric : ∃ ξ : genericPoints
      ((reducedPointClosure (X.fromSpecStalk (D.subschemeι x) q)).comap
        D.subschemeι).subscheme,
      ((reducedPointClosure (X.fromSpecStalk (D.subschemeι x) q)).comap
        D.subschemeι).subschemeι ξ.1 = x)
    (hdim : relativeDimension C.dimensionFunction
      (D.subschemeι ≫ p) x = k) :
    (cycleAssociatedToClosedSubscheme C (D.subschemeι ≫ p)
        ((reducedPointClosure (X.fromSpecStalk (D.subschemeι x) q)).comap
          D.subschemeι).subschemeι k).1 x =
      ((Module.length (X.presheaf.stalk (D.subschemeι x))
        (X.presheaf.stalk (D.subschemeι x) ⧸
          (Ideal.span {a} ⊔ q.asIdeal))).toNat : ℤ) := by
  change closedSubschemeCycleCoeff C (D.subschemeι ≫ p)
    ((reducedPointClosure (X.fromSpecStalk (D.subschemeι x) q)).comap
      D.subschemeι).subschemeι k x = _
  rw [closedSubschemeCycleCoeff_reducedPointClosure_comap_eq_length C
    (D.subschemeι ≫ p) D.subschemeι k x q hgeneric hdim]
  apply congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
  calc
    Module.length (D.subscheme.presheaf.stalk x)
          (D.subscheme.presheaf.stalk x ⧸
            Ideal.map (D.subschemeι.stalkMap x).hom q.asIdeal) =
        Module.length (X.presheaf.stalk (D.subschemeι x))
          (X.presheaf.stalk (D.subschemeι x) ⧸
            (q.asIdeal ⊔ RingHom.ker (D.subschemeι.stalkMap x).hom)) :=
      (length_quotient_sup_ker_eq_length_quotient_map
        (D.subschemeι.stalkMap x).hom
        (D.subschemeι.stalkMap_surjective x) q.asIdeal).symm
    _ = Module.length (X.presheaf.stalk (D.subschemeι x))
          (X.presheaf.stalk (D.subschemeι x) ⧸
            (Ideal.span {a} ⊔ q.asIdeal)) := by
      rw [hker, sup_comm]

/-- Reindex a sum over the subtype cut out by a predicate along an injection whose
image carries the predicate on the support of the summand. -/
lemma finsum_subtype_eq_finsum_mem_image {ι ι' M : Type*} [AddCommMonoid M]
    (f : ι → M) (P : ι → Prop) (g : ι' → ι) (S : Set ι') (hinj : Set.InjOn g S)
    (hP : ∀ y ∈ Function.support f, (P y ↔ y ∈ g '' S)) :
    (∑ᶠ y : {y : ι // P y}, f y.1) = ∑ᶠ q ∈ S, f (g q) := by
  have e1 : (∑ᶠ y : {y : ι // P y}, f y.1) = ∑ᶠ y ∈ {y : ι | P y}, f y :=
    finsum_set_coe_eq_finsum_mem _
  rw [e1, finsum_mem_inter_support_eq' f {y : ι | P y} (g '' S) hP, finsum_mem_image hinj]

/- The algebraic dictionary for the closed-subscheme formula: quotients of a
localization, nonzerodivisors in a principal ideal, and the minimal primes of the
support of a cyclic module. -/
/-- The natural map from `R ⧸ J` to `A ⧸ J A`. -/
private noncomputable def quotLocMap {R : Type u} [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] (J : Ideal R) :
    (R ⧸ J) →ₗ[R] (A ⧸ J.map (algebraMap R A)) :=
  Submodule.liftQ J
    ((Submodule.mkQ (J.map (algebraMap R A))).restrictScalars R ∘ₗ Algebra.linearMap R A)
    (fun x hx => by
      change Submodule.mkQ _ (algebraMap R A x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_map_of_mem _ hx)

private lemma quotLocMap_apply {R : Type u} [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] (J : Ideal R) (x : R) :
    quotLocMap A J (Ideal.Quotient.mk J x) = Ideal.Quotient.mk _ (algebraMap R A x) := rfl

private lemma isLocalizedModule_quotLoc {R : Type u} [CommRing R] (S : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A] (J : Ideal R) :
    IsLocalizedModule S (quotLocMap A J) := by
  have key : ∀ (r : R) (x : A ⧸ J.map (algebraMap R A)),
      (algebraMap R (Module.End R (A ⧸ J.map (algebraMap R A)))) r x =
        (algebraMap R A r) • x := by
    intro r x
    rw [Module.algebraMap_end_apply]
    exact (IsScalarTower.algebraMap_smul A r x).symm
  constructor
  · intro s
    have hs : IsUnit (algebraMap R A (s : R)) := IsLocalization.map_units A s
    obtain ⟨b, hb⟩ := hs.exists_right_inv
    rw [Module.End.isUnit_iff]
    constructor
    · intro m n hmn
      rw [key, key] at hmn
      exact hs.smul_left_cancel.mp hmn
    · intro m
      refine ⟨b • m, ?_⟩
      rw [key, smul_smul, hb, one_smul]
  · intro m
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj S a
    refine ⟨⟨Ideal.Quotient.mk J r, s⟩, ?_⟩
    dsimp only
    rw [Submonoid.smul_def, ← IsScalarTower.algebraMap_smul A (s : R), quotLocMap_apply,
      ← hrs, mul_comm]
    rfl
  · intro m n h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective n
    rw [quotLocMap_apply, quotLocMap_apply] at h
    have h' : algebraMap R A (a - b) ∈ J.map (algebraMap R A) := by
      rw [map_sub, ← Ideal.Quotient.eq]
      exact h
    obtain ⟨⟨i, s⟩, hi⟩ := (IsLocalization.mem_map_algebraMap_iff S A).mp h'
    rw [← map_mul] at hi
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists S A).mp hi
    refine ⟨t * s, ?_⟩
    have hmem : (t : R) * (s : R) * (a - b) ∈ J := by
      have h2 : (t : R) * ((a - b) * (s : R)) = (t : R) * (i : R) := ht
      have h4 : (t : R) * (s : R) * (a - b) = (t : R) * (i : R) := by rw [← h2]; ring
      rw [h4]
      exact Ideal.mul_mem_left _ _ i.2
    have heq : (Ideal.Quotient.mk J) ((t : R) * (s : R) * a) =
        (Ideal.Quotient.mk J) ((t : R) * (s : R) * b) := by
      rw [Ideal.Quotient.eq, ← mul_sub]
      exact hmem
    rw [Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul]
    simpa [Algebra.smul_def, mul_assoc] using heq

lemma mem_nonZeroDivisors_of_span_eq_span {R : Type*} [CommRing R] {b c : R}
    (h : Ideal.span {b} = Ideal.span {c}) (hc : c ∈ nonZeroDivisors R) :
    b ∈ nonZeroDivisors R := by
  have hbc : b ∈ Ideal.span ({c} : Set R) := h ▸ Ideal.mem_span_singleton_self b
  have hcb : c ∈ Ideal.span ({b} : Set R) := h.symm ▸ Ideal.mem_span_singleton_self c
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hbc
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hcb
  have hzero : (v * u - 1) * c = 0 := by
    rw [sub_mul, one_mul, mul_assoc, hu, hv, sub_self]
  have hvu : v * u = 1 := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hc).2 _ hzero)
  have huv : u * v = 1 := by rw [mul_comm]; exact hvu
  rw [← hu, mem_nonZeroDivisors_iff]
  have key : ∀ x : R, x * (u * c) = 0 → x = 0 := by
    intro x hx
    have h1 : (x * u) * c = 0 := by rw [mul_assoc]; exact hx
    have h2 : x * u = 0 := (mem_nonZeroDivisors_iff.mp hc).2 _ h1
    calc x = x * (u * v) := by rw [huv, mul_one]
      _ = (x * u) * v := by rw [mul_assoc]
      _ = 0 := by rw [h2, zero_mul]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

lemma isSMulRegular_self_of_mem_nonZeroDivisors {R : Type*} [CommRing R] {b : R}
    (hb : b ∈ nonZeroDivisors R) : IsSMulRegular R b := by
  intro x y hxy
  have h : b * x = b * y := hxy
  have h2 : (x - y) * b = 0 := by
    rw [sub_mul, mul_comm x b, mul_comm y b, h, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hb).2 (x - y) h2)

lemma isSMulRegular_quotient_ker {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hsurj : Function.Surjective φ) (a : A)
    (h : IsSMulRegular B (φ a)) : IsSMulRegular (A ⧸ RingHom.ker φ) a := by
  let ψ := RingHom.quotientKerEquivOfSurjective hsurj
  have hψ : ∀ x : A, ψ (Ideal.Quotient.mk (RingHom.ker φ) x) = φ x := fun x => rfl
  have hsmul : ∀ (x : A) (m : A ⧸ RingHom.ker φ), ψ (x • m) = φ x * ψ m := by
    intro x m
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [hψ]
    have : x • (Ideal.Quotient.mk (RingHom.ker φ) y) = Ideal.Quotient.mk _ (x * y) := rfl
    rw [this, hψ, map_mul]
  intro m n hmn
  have hmn' : a • m = a • n := hmn
  apply ψ.injective
  refine h ?_
  change φ a * ψ m = φ a * ψ n
  rw [← hsmul, ← hsmul, hmn']

lemma ne_closedPoint_of_minimal_support_quotient {R : Type*} [CommRing R]
    [IsLocalRing R] (I : Ideal R) (hI : ringKrullDim (R ⧸ I) = 1)
    (q : PrimeSpectrum R) (hq : Minimal (· ∈ Module.support R (R ⧸ I)) q) :
    q ≠ IsLocalRing.closedPoint R := by
  have hM : Module.supportDim R (R ⧸ I) = 1 := by
    rw [Module.supportDim_quotient_eq_ringKrullDim, hI]
  exact ((Set.ext_iff.mp (AlgebraicGeometry.minimal_support_eq_nonclosed hM) q).mp hq).2

theorem effectiveCartier_affine_generator {X : Scheme.{u}}
    (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (x : X) (hx : x ∈ I.supportSet) :
    ∃ (U : X.affineOpens), x ∈ U.1 ∧
      ∃ f : Γ(X, U.1), IsRegular f ∧ I.ideal U = Ideal.span {f} := by
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal I).mp hI x hx
  exact ⟨⟨U, hU⟩, hxU, f, hf,
    Stacks.Divisors.ideal_eq_quotient_of_chart I U hU (Ideal.span {f}) e he⟩



/- The length of the quotient of the local ring by the stalk of an ideal sheaf, at a
point of the fibre of `Scheme.fromSpecStalk` at `z`, is the length of the localization
at the corresponding prime of the quotient at `z`. This is the closed-subscheme twin of
`length_stalk_fromSpecStalk_eq_length_localized`. -/
lemma length_quotient_stalk_fromSpecStalk_eq_length_localized
    {X : Scheme.{u}} (I : X.IdealSheafData) (z : X)
    (q : PrimeSpectrum (X.presheaf.stalk z)) :
    Module.length (X.presheaf.stalk (X.fromSpecStalk z q))
        (X.presheaf.stalk (X.fromSpecStalk z q) ⧸
          IdealSheafData.stalk I (X.fromSpecStalk z q)) =
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl
          (X.presheaf.stalk z ⧸ IdealSheafData.stalk I z)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hyU : X.fromSpecStalk z q ∈ U := (specializes_fromSpecStalk z q).mem_open U.2 hzU
  let : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  let : Algebra Γ(X, U) (X.presheaf.stalk (X.fromSpecStalk z q)) :=
    (X.presheaf.germ U (X.fromSpecStalk z q) hyU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk z)
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := hU.isLocalization_stalk ⟨z, hzU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk z q))
      (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨X.fromSpecStalk z q, hyU⟩
  have := isLocalizedModule_quotLoc (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
    (X.presheaf.stalk z) (I.ideal ⟨U, hU⟩)
  have := isLocalizedModule_quotLoc
    (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal.primeCompl
    (X.presheaf.stalk (X.fromSpecStalk z q)) (I.ideal ⟨U, hU⟩)
  have hpy : (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal =
      Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk z)) q.asIdeal :=
    primeIdealOf_fromSpecStalk hU z hzU q hyU
  have hT : (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal.primeCompl =
      q.asIdeal.primeCompl.comap (algebraMap Γ(X, U) (X.presheaf.stalk z)) := by
    ext r
    change r ∉ (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal ↔
      algebraMap Γ(X, U) (X.presheaf.stalk z) r ∉ q.asIdeal
    rw [hpy]
    rfl
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I z ⟨U, hU⟩ hzU,
    AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I (X.fromSpecStalk z q) ⟨U, hU⟩ hyU]
  exact length_eq_of_localized_at_prime (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
    (quotLocMap (X.presheaf.stalk z) (I.ideal ⟨U, hU⟩)) q.asIdeal
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl _)
    (hU.primeIdealOf ⟨X.fromSpecStalk z q, hyU⟩).asIdeal.primeCompl hT
    (quotLocMap (X.presheaf.stalk (X.fromSpecStalk z q)) (I.ideal ⟨U, hU⟩))

/- A point of the fibre of `Scheme.fromSpecStalk` at `z` lies in the support of an
ideal sheaf exactly when the corresponding prime lies in the support of the quotient
of the local ring at `z`. -/
lemma mem_support_fromSpecStalk_iff {X : Scheme.{u}} (I : X.IdealSheafData) (z : X)
    (q : PrimeSpectrum (X.presheaf.stalk z)) :
    X.fromSpecStalk z q ∈ (I.support : Set X) ↔
      q ∈ Module.support (X.presheaf.stalk z)
        (X.presheaf.stalk z ⧸ IdealSheafData.stalk I z) := by
  have hlen := length_quotient_stalk_fromSpecStalk_eq_length_localized I z q
  have h1 : Module.length (X.presheaf.stalk (X.fromSpecStalk z q))
        (X.presheaf.stalk (X.fromSpecStalk z q) ⧸
          IdealSheafData.stalk I (X.fromSpecStalk z q)) = 0 ↔
      Subsingleton (X.presheaf.stalk (X.fromSpecStalk z q) ⧸
        IdealSheafData.stalk I (X.fromSpecStalk z q)) := Module.length_eq_zero_iff
  have h2 : Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl
          (X.presheaf.stalk z ⧸ IdealSheafData.stalk I z)) = 0 ↔
      Subsingleton (LocalizedModule q.asIdeal.primeCompl
        (X.presheaf.stalk z ⧸ IdealSheafData.stalk I z)) := Module.length_eq_zero_iff
  have key : Nontrivial (X.presheaf.stalk (X.fromSpecStalk z q) ⧸
        IdealSheafData.stalk I (X.fromSpecStalk z q)) ↔
      Nontrivial (LocalizedModule q.asIdeal.primeCompl
        (X.presheaf.stalk z ⧸ IdealSheafData.stalk I z)) := by
    rw [← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton,
      ← h1, ← h2, hlen]
  refine Iff.trans ?_ key
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, Ideal.Quotient.subsingleton_iff,
    Stacks.Divisors.stalk_eq_top_iff_notMem_support]
  rfl

/- A point of the support of a closed subscheme of dimension at most `k + 1` which
strictly specialises to a point of relative dimension `k` has relative dimension
`k + 1`. -/
lemma relativeDimension_eq_succ_of_specializes_support
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    {y z : X} (hy : y ∈ (Z.support : Set X)) (hspec : y ⤳ z) (hne : y ≠ z)
    (hz : relativeDimension C.dimensionFunction p z = k) :
    relativeDimension C.dimensionFunction p y = k + 1 := by
  have hlt := relativeDimension_lt_of_specializes C p hspec hne
  rw [hz] at hlt
  obtain ⟨y', rfl⟩ := exists_subschemeι_eq_of_mem_support Z hy
  have hle := (relativeDimension_le_closedSubschemeDimension_at C p Z.subschemeι y').trans hZ
  have hle' : relativeDimension C.dimensionFunction p (Z.subschemeι y') ≤ k + 1 :=
    WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hle)
  omega

/- Specialisation is reflected by a closed immersion. -/
private lemma specializes_of_specializes_image {T Y : Scheme.{u}} (j : T ⟶ Y)
    [IsClosedImmersion j] {a b : T} (h : j a ⤳ j b) : a ⤳ b := by
  rw [specializes_iff_mem_closure] at h ⊢
  rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq] at h
  obtain ⟨a', ha', hja'⟩ := h
  rwa [j.isClosedEmbedding.injective hja'] at ha'

/- The scheme-theoretic intersection of two closed subschemes seen from either side:
a generic point of a component of `Z ∩ D` inside `D` is the image of a generic point of
a component of `D ∩ Z` inside `Z`, with the same image in the ambient scheme. -/
lemma exists_genericPoint_comap_symm {X : Scheme.{u}} (Z D : X.IdealSheafData)
    (x : (Z.comap D.subschemeι).subscheme)
    (hx : closure ({x} : Set (Z.comap D.subschemeι).subscheme) ∈
      irreducibleComponents (Z.comap D.subschemeι).subscheme) :
    ∃ ξ : genericPoints (D.comap Z.subschemeι).subscheme,
      Z.subschemeι ((D.comap Z.subschemeι).subschemeι ξ.1) =
        D.subschemeι ((Z.comap D.subschemeι).subschemeι x) := by
  classical
  have hmax : ∀ v : X, v ∈ (Z.support : Set X) → v ∈ (D.support : Set X) →
      v ⤳ D.subschemeι ((Z.comap D.subschemeι).subschemeι x) →
      v = D.subschemeι ((Z.comap D.subschemeι).subschemeι x) := by
    intro v hvZ hvD hspec
    obtain ⟨v₁, rfl⟩ := exists_subschemeι_eq_of_mem_support D hvD
    have hv₁E : v₁ ∈ ((Z.comap D.subschemeι).support : Set D.subscheme) := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hvZ
    obtain ⟨v₂, rfl⟩ := exists_subschemeι_eq_of_mem_support _ hv₁E
    have hv₂spec : v₂ ⤳ x :=
      specializes_of_specializes_image (Z.comap D.subschemeι).subschemeι
        (specializes_of_specializes_image D.subschemeι hspec)
    rw [eq_of_specializes_of_closure_mem_irreducibleComponents hx hv₂spec]
  obtain ⟨z₁, hz₁⟩ := exists_subschemeι_eq_of_mem_support Z
    (subschemeι_comap_mem_support Z D x)
  have hz₁F : z₁ ∈ ((D.comap Z.subschemeι).support : Set Z.subscheme) := by
    rw [Scheme.IdealSheafData.support_comap]
    change Z.subschemeι z₁ ∈ (D.support : Set X)
    rw [hz₁]
    exact subschemeι_mem_support D _
  obtain ⟨ξ₀, hξ₀⟩ := exists_subschemeι_eq_of_mem_support _ hz₁F
  refine ⟨⟨ξ₀, closure_mem_irreducibleComponents_of_specializes_eq fun η hη => ?_⟩,
    by rw [hξ₀, hz₁]⟩
  have h1 : Z.subschemeι ((D.comap Z.subschemeι).subschemeι η) ⤳
      Z.subschemeι ((D.comap Z.subschemeι).subschemeι ξ₀) :=
    (hη.map (D.comap Z.subschemeι).subschemeι.continuous).map Z.subschemeι.continuous
  have h5 := hmax _ (subschemeι_mem_support Z _) (subschemeι_comap_mem_support D Z η)
    (by rw [hξ₀, hz₁] at h1; exact h1)
  exact (D.comap Z.subschemeι).subschemeι.isEmbedding.injective
    (Z.subschemeι.isEmbedding.injective (by rw [h5, hξ₀, hz₁]))

end Stacks.Chow
