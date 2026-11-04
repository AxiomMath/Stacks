module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionLocal

/-!
# Uniqueness of the ideal of Stacks 0GHE over a chart

The ideal `J` produced over an affine chart `Spec A` of the base by
`AlgebraicGeometry.Artin.ContractionSituation.exists_chartIdeal` is determined by the points it
classifies: an element of `A` vanishing at every affine point of `U'` and at every affine point
of `W` lying over `Z` lies in `J`. The proof is the Krull argument of the source's gluing step:
modulo `J` such an element lies in every power of `I` (test against `Spec (A ⧸ J + I ^ (n+1))`,
a point of `W`) and is killed by a power of `I` (test against `Spec (A_b ⧸ J A_b)` for `b ∈ I`, a
point of `U'`), hence vanishes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An object of the site over `S` is *good* for the situation when it is a point of `U'`, or a
point of `W` lying over `Z`. These are the points at which the ideal of Stacks 0GHE vanishes. -/
def IsGoodPoint (c : ContractionSituation B S hS)
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (V : BigFppfOver B S hS) : Prop :=
  Nonempty (c.U'.toFunctor.obj (Opposite.op V)) ∨
    (Nonempty (c.W.obj.obj (Opposite.op V)) ∧
      Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆ Z)

/-- The morphism of affine charts induced by a ring map. -/
noncomputable def affineHom {A A' : Type u} [CommRing A] [CommRing A']
    {hA : B.Contains (Spec (.of A))} (hA' : B.Contains (Spec (.of A'))) (f : Spec (.of A) ⟶ S)
    (φ : A →+* A') :
    FormalSpace.affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ f) ⟶
      FormalSpace.affineOver B S hS hA f :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ)))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The chart ring map of `affineHom hA' f φ` sends `a` to `φ a`, viewed as a global section of
`Spec A'` through `Scheme.ΓSpecIso`. -/
theorem chartRing_affineHom {A A' : Type u} [CommRing A] [CommRing A']
    {hA : B.Contains (Spec (.of A))} (hA' : B.Contains (Spec (.of A'))) (f : Spec (.of A) ⟶ S)
    (φ : A →+* A') (a : A) :
    FormalSpace.chartRing (affineHom (hS := hS) (hA := hA) hA' f φ) a =
      (Scheme.ΓSpecIso (CommRingCat.of A')).inv (φ a) :=
  (congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

/-- **The Krull argument.** Over an affine chart `Spec A`, let `J` have properties (1) and (3) of
`exists_chartIdeal` for an ideal `I` such that points killing a power of `I` lie over `Z`. An
element of `A` vanishing at every good affine point lies in `J`. -/
theorem mem_of_forall_isGoodPoint (c : ContractionSituation B S hS)
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    {A : Type u} [CommRing A] [IsNoetherianRing A] {hA : B.Contains (Spec (.of A))}
    {f : Spec (.of A) ⟶ S} (I J : Ideal A)
    (hZpts : ∀ (V : BigFppfOver B S hS) (v : V ⟶ FormalSpace.affineOver B S hS hA f) (n : ℕ),
      I ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) →
        Set.range (Space.pointsMap B S hS (yoneda.obj V) (terminal.from (yoneda.obj V))) ⊆ Z)
    (h1 : ∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
        (v : V ⟶ FormalSpace.affineOver B S hS hA f),
          J ≤ RingHom.ker (FormalSpace.chartRing v) → I.map (FormalSpace.chartRing v) = ⊤ →
            Nonempty (c.U'.toFunctor.obj (Opposite.op V)))
    (h3 : ∀ (V : BigFppfOver B S hS) (v : V ⟶ FormalSpace.affineOver B S hS hA f) (n : ℕ),
          J ≤ RingHom.ker (FormalSpace.chartRing v) →
            I ^ (n + 1) ≤ RingHom.ker (FormalSpace.chartRing v) →
              Nonempty (c.W.obj.obj (Opposite.op V)))
    (x : A)
    (hx : ∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (v : V ⟶ FormalSpace.affineOver B S hS hA f), c.IsGoodPoint Z V →
        FormalSpace.chartRing v x = 0) :
    x ∈ J := by
  classical
  let mk := Ideal.Quotient.mk J
  -- `x` lies in every power of `I` modulo `J`
  have hpow : ∀ n, mk x ∈ (I.map mk) ^ n := by
    intro n
    cases n with
    | zero => simp
    | succ m =>
      let K := J ⊔ I ^ (m + 1)
      let T := (BigAffineFppf.inclusion B S hS).obj (FormalSpace.quotientOver B S hS f hA K)
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
        (FormalSpace.quotientOver B S hS f hA K).property
      let t := Space.quotientToAffineOver B S hS f hA K
      have hker : RingHom.ker (FormalSpace.chartRing t) = K :=
        ker_chartRing_quotientToAffineOver K
      have hgood : c.IsGoodPoint Z T := Or.inr
        ⟨h3 T t m (by rw [hker]; exact le_sup_left) (by rw [hker]; exact le_sup_right),
          hZpts T t m (by rw [hker]; exact le_sup_right)⟩
      have hxK : x ∈ K := by rw [← hker]; exact RingHom.mem_ker.2 (hx T t hgood)
      obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.1 hxK
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hy
  -- `x` is killed by a power of `I` modulo `J`
  have hrad : I.map mk ≤ (Ideal.span {mk x}).annihilator.radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    let Ab := Localization.Away b
    let φ : A →+* Ab ⧸ J.map (algebraMap A Ab) :=
      (Ideal.Quotient.mk _).comp (algebraMap A Ab)
    have hAb : B.Contains (Spec (.of Ab)) :=
      B.contains_of_isOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A Ab))) hA
    have hR : B.Contains (Spec (.of (Ab ⧸ J.map (algebraMap A Ab)))) :=
      FormalSpace.contains_spec_quotient B hAb _
    let T := FormalSpace.affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ f)
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
      inferInstanceAs (IsAffine (Spec _))
    let t : T ⟶ FormalSpace.affineOver B S hS hA f := affineHom hR f φ
    have hrt : ∀ a, FormalSpace.chartRing t a = 0 ↔ φ a = 0 := fun a => by
      rw [chartRing_affineHom]
      constructor
      · intro h
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Ab ⧸ J.map (algebraMap A Ab)))).hom h
        rw [Iso.inv_hom_id_apply] at this
        exact this.trans ((Scheme.ΓSpecIso
          (CommRingCat.of (Ab ⧸ J.map (algebraMap A Ab)))).hom.hom.map_zero)
      · intro h
        rw [h]
        exact map_zero _
    have hJ : J ≤ RingHom.ker (FormalSpace.chartRing t) := fun a ha => by
      rw [RingHom.mem_ker, hrt]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    have hI : I.map (FormalSpace.chartRing t) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have hunit : IsUnit (FormalSpace.chartRing t b) := by
        rw [chartRing_affineHom]
        exact (IsLocalization.Away.algebraMap_isUnit b).map (Ideal.Quotient.mk _) |>.map _
      obtain ⟨y, hy⟩ := hunit.exists_left_inv
      rw [← hy]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hb)
    have hxt := hx T t (Or.inl (h1 T t hJ hI))
    rw [hrt] at hxt
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers b) Ab J x).1 (Ideal.Quotient.eq_zero_iff_mem.1 hxt)
    refine Ideal.mem_comap.2 ⟨m, ?_⟩
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, ← map_pow, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad
    (Ideal.fg_of_isNoetherianRing _)
  have h0 : mk x = 0 := Ideal.eq_zero_of_forall_mem_pow_of_pow_mul_eq_zero (I.map mk) hpow
    (k := k) fun y hy => by
      have := hk hy
      rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at this
      exact this
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

end AlgebraicGeometry.Artin.ContractionSituation
