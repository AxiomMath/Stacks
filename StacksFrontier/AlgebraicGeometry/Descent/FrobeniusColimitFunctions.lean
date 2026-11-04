module

public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimitHSheaf
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal

/-!
# Frobenius-twisted functions along a proper morphism with geometrically connected fibres

Let `p` be a prime and let `f : X ⟶ V` be a proper surjective morphism with geometrically connected
fibres onto an affine scheme in characteristic `p`. This file proves the two halves of the
statement at the heart of the full faithfulness part of Stacks Tag 0EXH, namely that

`colim_F Γ(V, 𝒪_V) ⟶ colim_F Γ(X, 𝒪_X)`

is bijective:

* `AlgebraicGeometry.exists_pow_prime_pow_eq_zero_of_appTop_eq_zero`: a function on `V` whose
  pullback vanishes is killed by a `p`-power Frobenius (this only uses surjectivity);
* `AlgebraicGeometry.exists_pow_prime_pow_eq_appTop_of_geometricallyConnected`: every function on
  `X` has a `p`-power which is pulled back from `V`.

The argument for the second is the one of the source. The two pullbacks of a function `g` on `X`
to `X ×_V X` agree at every point: at a point `z` with residue field `K`, the base change `X_K` is
proper and connected over `K`, so its ring of functions is local
(`isArtinianRing_and_isLocalRing_globalSections_of_connectedSpace` in
`Stacks.AlgebraicGeometry.ProperSectionsGeom`),
and the two `K`-points of `X_K` given by `z` induce the same map on functions
(`AlgebraicGeometry.ringHom_eq_of_comp_eq_id_of_isLocalRing`). Hence the difference of the two
pullbacks is nilpotent, so the pullback of `g` to the absolute weak normalization descends along
the proper surjection (Stacks Tag 0EVT,
`AlgebraicGeometry.existsUnique_properSurjective_glue_section`),
and a section of the absolute weak normalization of the affine `V` has a `p`-power coming from `V`
(Stacks Tag 0EVW).

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 0EVT](https://stacks.math.columbia.edu/tag/0EVT)
* [Stacks Project, Tag 0EVW](https://stacks.math.columbia.edu/tag/0EVW)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **Two sections of a local algebra over a field agree.** If `ρ : K →+* R` is a ring map from a
field to a local ring and `σ₁, σ₂ : R →+* K` are both left inverse to it, then `σ₁ = σ₂`: both
kernels are maximal, hence the maximal ideal, and `a - ρ (σ₁ a)` lies in it. -/
theorem ringHom_eq_of_comp_eq_id_of_isLocalRing {K R : Type*} [Field K] [CommRing R]
    [IsLocalRing R] (ρ : K →+* R) (σ₁ σ₂ : R →+* K) (h₁ : σ₁.comp ρ = RingHom.id K)
    (h₂ : σ₂.comp ρ = RingHom.id K) : σ₁ = σ₂ := by
  have hsurj (σ : R →+* K) (h : σ.comp ρ = RingHom.id K) : Function.Surjective σ :=
    fun c ↦ ⟨ρ c, by simpa using congrArg (fun φ ↦ φ c) h⟩
  have hker (σ : R →+* K) (h : σ.comp ρ = RingHom.id K) :
      RingHom.ker σ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective σ (hsurj σ h))
  ext a
  have hρ₁ : σ₁ (ρ (σ₁ a)) = σ₁ a := by simpa using congrArg (fun φ ↦ φ (σ₁ a)) h₁
  have hρ₂ : σ₂ (ρ (σ₁ a)) = σ₁ a := by simpa using congrArg (fun φ ↦ φ (σ₁ a)) h₂
  have hmem : a - ρ (σ₁ a) ∈ RingHom.ker σ₂ := by
    rw [hker σ₂ h₂, ← hker σ₁ h₁, RingHom.mem_ker, map_sub, hρ₁, sub_self]
  rw [RingHom.mem_ker, map_sub, hρ₂, sub_eq_zero] at hmem
  exact hmem.symm

/-! ### Copies of the Frobenius root machinery of Stacks 0EVW -/



@[instance_reducible]
private noncomputable def zmodAlgebraOfCastEqZero' (p : ℕ) [Fact p.Prime] (R : Type*)
    [CommRing R] (hp : (p : R) = 0) : Algebra (ZMod p) R := by
  classical
  by_cases hR : Nontrivial R
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp
    exact RingHom.toAlgebra (ZMod.castHom (dvd_refl p) R)
  · haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact RingHom.toAlgebra
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ => Subsingleton.elim _ _ }

section AffineRoots

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Frobenius roots on the absolute weak normalization of an affine scheme** in characteristic
`p` (Stacks Tag 0EVW): every global function on `Zᵃʷⁿ` has a `p ^ n`-th power pulled back from
`Z`. -/
private theorem exists_pow_eq_appTop_absoluteWeakNormalizationHom {Z : Scheme.{u}} [IsAffine Z]
    (hZ : (p : Γ(Z, ⊤)) = 0) (g : Γ(Z.absoluteWeakNormalization, ⊤)) :
    ∃ (n : ℕ) (a : Γ(Z, ⊤)), g ^ p ^ n = Z.absoluteWeakNormalizationHom.appTop a := by
  let Y := Z.absoluteWeakNormalization
  let q := Z.absoluteWeakNormalizationHom
  have hY : IsAbsolutelyWeaklyNormal Y := by
    let awn : UniversalHomeomorphismOver Z := initial (UniversalHomeomorphismOver Z)
    refine (isIso_initialTo_iff_isAbsolutelyWeaklyNormal Z awn).mp ?_
    rw [show initial.to awn = 𝟙 awn from Subsingleton.elim _ _]
    show IsIso (𝟙 awn.obj.left)
    infer_instance
  have halg : ∀ (A : Type u) [CommRing A] [Algebra (ZMod p) A]
      (r : Algebra.AbsoluteWeakNormalization A),
      ∃ (n : ℕ) (a : A), r ^ p ^ n = algebraMap A (Algebra.AbsoluteWeakNormalization A) a := by
    intro A _ _ r
    obtain ⟨e, he, -⟩ :=
      Algebra.existsUnique_frobeniusColimit_iso_absoluteWeakNormalization p hp.out A
    obtain ⟨n, a, ha⟩ := Algebra.frobeniusColimit_exists_rep p A (e.inv r)
    refine ⟨n, a, ?_⟩
    let D := Algebra.frobeniusDiagram p A
    let ιn : A →+* ↑(colimit D) := (colimit.ι D n).hom
    let ι0 : A →+* ↑(colimit D) := (colimit.ι D 0).hom
    let eR : ↑(colimit D) →+* Algebra.AbsoluteWeakNormalization A := e.hom.hom
    have hr : r = eR (ιn a) := by
      show r = e.hom (colimit.ι D n a)
      rw [ha]
      exact (Iso.inv_hom_id_apply e r).symm
    have h0 : eR (ι0 a) = algebraMap A (Algebra.AbsoluteWeakNormalization A) a :=
      congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of (Algebra.AbsoluteWeakNormalization A) =>
        φ.hom a) he
    have hpow : ιn a ^ p ^ n = ι0 a :=
      (map_pow ιn a (p ^ n)).symm.trans (Algebra.frobeniusColimit_ι_zero_pow p A n a).symm
    rw [hr, ← map_pow, hpow, h0]
  let := zmodAlgebraOfCastEqZero' p Γ(Z, ⊤) hZ
  let A := Γ(Z, ⊤)
  let R := Algebra.AbsoluteWeakNormalization A
  let φ : CommRingCat.of A ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap A R)
  let q' : Spec (.of R) ⟶ Z := Spec.map φ ≫ Z.isoSpec.inv
  have hiso : UniversalHomeomorphism Z.isoSpec.inv :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  have hq' : UniversalHomeomorphism q' :=
    universalHomeomorphism_comp _ _ (absoluteWeakNormalization_universalHomeomorphism A) hiso
  let Y₁ : UniversalHomeomorphismOver Z :=
    ⟨Over.mk q, universalHomeomorphism_absoluteWeakNormalizationHom Z⟩
  let Y₂ : UniversalHomeomorphismOver Z := ⟨Over.mk q', hq'⟩
  have hRawn : IsAbsolutelyWeaklyNormalRing R :=
    Algebra.isAbsolutelyWeaklyNormalRing_of_isTerminal A
      (Algebra.absoluteWeakNormalizationCandidate A)
      (Algebra.absoluteWeakNormalizationCandidate_isTerminal A)
  have hY₂ : IsAbsolutelyWeaklyNormal Y₂.obj.left := by
    intro x
    refine ⟨⟨⊤, isAffineOpen_top (Spec (.of R))⟩, Set.mem_univ _, ?_⟩
    show IsAbsolutelyWeaklyNormalRing Γ(Spec (.of R), ⊤)
    exact absolutelyWeaklyNormalRing_of_ringEquiv
      ((Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv) hRawn
  let i₁ : Z.absoluteWeakNormalization ⟶ Y := (initial.to Y₁).hom.left
  let i₂ : Z.absoluteWeakNormalization ⟶ Spec (.of R) := (initial.to Y₂).hom.left
  have hi₁ : IsIso i₁ := (isIso_initialTo_iff_isAbsolutelyWeaklyNormal Z Y₁).mpr hY
  have hi₂ : IsIso i₂ := (isIso_initialTo_iff_isAbsolutelyWeaklyNormal Z Y₂).mpr hY₂
  have hw₁ : i₁ ≫ q = Z.absoluteWeakNormalizationHom := (initial.to Y₁).hom.w
  have hw₂ : i₂ ≫ q' = Z.absoluteWeakNormalizationHom := (initial.to Y₂).hom.w
  let j : Y ⟶ Spec (.of R) := inv i₁ ≫ i₂
  have hj : j ≫ q' = q := by rw [Category.assoc, hw₂, ← hw₁, IsIso.inv_hom_id_assoc]
  have hjiso : IsIso j := inferInstance
  let r : R := (Scheme.ΓSpecIso (.of R)).hom ((inv j).appTop g)
  obtain ⟨n, a, hra⟩ := halg A r
  refine ⟨n, a, ?_⟩
  have hinvSpec : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(Z, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ]
    rfl
  have hqa : q.appTop a = j.appTop ((Scheme.ΓSpecIso (.of R)).inv (algebraMap A R a)) := by
    rw [← hj, Scheme.Hom.comp_appTop]
    show j.appTop ((Spec.map φ).appTop (Z.isoSpec.inv.appTop a)) = _
    rw [hinvSpec]
    congr 1
    exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) a).symm
  rw [hqa, ← hra, map_pow, map_pow]
  show g ^ p ^ n = (j.appTop ((Scheme.ΓSpecIso (.of R)).inv
    ((Scheme.ΓSpecIso (.of R)).hom ((inv j).appTop g)))) ^ p ^ n
  rw [Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    IsIso.hom_inv_id]
  rfl

end AffineRoots

/-! ### Injectivity -/

/-- Pulling back a global function along two factorizations of the same morphism agrees. -/
private theorem appTop_apply_eq_of_comp_eq {A B C D : Scheme.{u}} {f : A ⟶ B} {g : B ⟶ D}
    {f' : A ⟶ C} {g' : C ⟶ D} (h : f ≫ g = f' ≫ g') (x : Γ(D, ⊤)) :
    f.appTop (g.appTop x) = f'.appTop (g'.appTop x) := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply]

/-- The preimage of the basic open of a function whose pullback vanishes is empty. -/
private theorem preimage_basicOpen_eq_bot_of_appTop_eq_zero {X S : Scheme.{u}} (f : X ⟶ S)
    (a : Γ(S, ⊤)) (ha : f.appTop a = 0) : f ⁻¹ᵁ S.basicOpen a = ⊥ := by
  rw [Scheme.preimage_basicOpen]
  show X.basicOpen (f.appTop a) = ⊥
  rw [ha, Scheme.basicOpen_zero]

/-- A global function on a quasi-compact scheme whose pullback along a surjective morphism
vanishes is nilpotent. -/
theorem isNilpotent_of_appTop_eq_zero {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    [CompactSpace S] (a : Γ(S, ⊤)) (ha : f.appTop a = 0) : IsNilpotent a := by
  refine (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    (U := (⊤ : S.Opens)) isCompact_univ a).mpr ?_
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hx : x ∈ f ⁻¹ᵁ S.basicOpen a := hy
  rwa [preimage_basicOpen_eq_bot_of_appTop_eq_zero f a ha] at hx

/-- **Injectivity of `colim_F Γ(S, 𝒪_S) ⟶ colim_F Γ(X, 𝒪_X)` along a surjection.** A global
function on a quasi-compact scheme in characteristic `p` whose pullback along a surjective
morphism vanishes is killed by some `p`-power Frobenius. -/
theorem exists_pow_prime_pow_eq_zero_of_appTop_eq_zero (p : ℕ) [Fact p.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [CompactSpace S] (a : Γ(S, ⊤))
    (ha : f.appTop a = 0) : ∃ k : ℕ, a ^ p ^ k = 0 :=
  let ⟨m, hm⟩ := isNilpotent_of_appTop_eq_zero f a ha
  ⟨m, pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hm⟩

/-! ### The two pullbacks to the fibre square agree up to nilpotents -/

open Stacks.AlgebraicGeometry.ProperSectionsGeom in
/-- **The two pullbacks of a function to the fibre square agree up to a nilpotent.** Let
`f : X ⟶ V` be proper with geometrically connected fibres and `X` quasi-compact. For a global
function `g` on `X`, the difference of its two pullbacks to `X ×_V X` vanishes at every point,
hence is nilpotent. At a point `z` with residue field `K`, the two `K`-points of the base change
`X_K` determined by `z` induce the same map on global functions, because `Γ(X_K, 𝒪)` is local
(`X_K` being proper and connected over `K`). -/
theorem isNilpotent_fst_appTop_sub_snd_appTop {X V : Scheme.{u}} (f : X ⟶ V) [IsProper f]
    [GeometricallyConnected f] [CompactSpace X] (g : Γ(X, ⊤)) :
    IsNilpotent ((pullback.fst f f).appTop g - (pullback.snd f f).appTop g) := by
  have : CompactSpace ((Limits.pullback f f : Scheme.{u}) : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  refine (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    (U := (⊤ : (pullback f f).Opens)) isCompact_univ _).mpr ?_
  refine eq_bot_iff.mpr fun z hz => ?_
  let K := (pullback f f).residueField z
  let ι : Spec K ⟶ pullback f f := (pullback f f).fromSpecResidueField z
  let q : Spec K ⟶ V := ι ≫ pullback.fst f f ≫ f
  let σ₁ : Spec K ⟶ pullback f q := pullback.lift (ι ≫ pullback.fst f f) (𝟙 _)
    (by simp [q])
  let σ₂ : Spec K ⟶ pullback f q := pullback.lift (ι ≫ pullback.snd f f) (𝟙 _)
    (by simp [q, pullback.condition])
  have hconn : ConnectedSpace ((Limits.pullback f q : Scheme.{u}) : Type u) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) q (pullback.fst f q)
      (pullback.snd f q) (IsPullback.of_hasPullback f q)
  have hloc : IsLocalRing Γ(pullback f q, ⊤) :=
    (isArtinianRing_and_isLocalRing_globalSections_of_connectedSpace K (pullback.snd f q)).2
  let ρ : K →+* Γ(pullback f q, ⊤) :=
    ((Scheme.ΓSpecIso K).inv ≫ (pullback.snd f q).appTop).hom
  let τ (σ : Spec K ⟶ pullback f q) : Γ(pullback f q, ⊤) →+* K :=
    (σ.appTop ≫ (Scheme.ΓSpecIso K).hom).hom
  have hsec (σ : Spec K ⟶ pullback f q) (hσ : σ ≫ pullback.snd f q = 𝟙 _) :
      (τ σ).comp ρ = RingHom.id K := by
    have h : ((Scheme.ΓSpecIso K).inv ≫ (pullback.snd f q).appTop) ≫
        σ.appTop ≫ (Scheme.ΓSpecIso K).hom = 𝟙 _ := by
      rw [Category.assoc, ← Category.assoc (pullback.snd f q).appTop, ← Scheme.Hom.comp_appTop,
        hσ, Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]
    exact congrArg CommRingCat.Hom.hom h
  have hτ : τ σ₁ = τ σ₂ :=
    ringHom_eq_of_comp_eq_id_of_isLocalRing ρ (τ σ₁) (τ σ₂)
      (hsec σ₁ (pullback.lift_snd _ _ _)) (hsec σ₂ (pullback.lift_snd _ _ _))
  have hval (σ : Spec K ⟶ pullback f q) (π : pullback f f ⟶ X)
      (hσ : σ ≫ pullback.fst f q = ι ≫ π) :
      τ σ ((pullback.fst f q).appTop g) = (Scheme.ΓSpecIso K).hom (ι.appTop (π.appTop g)) := by
    show (σ.appTop ≫ (Scheme.ΓSpecIso K).hom) ((pullback.fst f q).appTop g) = _
    rw [ConcreteCategory.comp_apply, appTop_apply_eq_of_comp_eq hσ]
  have heq : ι.appTop ((pullback.fst f f).appTop g - (pullback.snd f f).appTop g) = 0 := by
    have h₁ := hval σ₁ (pullback.fst f f) (pullback.lift_fst _ _ _)
    have h₂ := hval σ₂ (pullback.snd f f) (pullback.lift_fst _ _ _)
    rw [hτ] at h₁
    rw [map_sub, sub_eq_zero]
    exact (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.injective (h₁.symm.trans h₂)
  obtain ⟨s⟩ : Nonempty (Spec K) := inferInstance
  have hs : s ∈ ι ⁻¹ᵁ (pullback f f).basicOpen
      ((pullback.fst f f).appTop g - (pullback.snd f f).appTop g) := by
    rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
    exact hz
  rwa [preimage_basicOpen_eq_bot_of_appTop_eq_zero ι _ heq] at hs

/-! ### Surjectivity -/

/-- **Surjectivity of `colim_F Γ(V, 𝒪_V) ⟶ colim_F Γ(X, 𝒪_X)`**, the substantial half of the
statement behind the full faithfulness in Stacks Tag 0EXH. Let `V` be an affine scheme in
characteristic `p` and `f : X ⟶ V` proper and surjective with geometrically connected fibres.
Then every global function on `X` has a `p ^ n`-th power pulled back from `V`. -/
theorem exists_pow_prime_pow_eq_appTop_of_geometricallyConnected (p : ℕ) [Fact p.Prime]
    {X V : Scheme.{u}} [IsAffine V] (hV : (p : Γ(V, ⊤)) = 0) (f : X ⟶ V) [IsProper f]
    [Surjective f] [GeometricallyConnected f] (g : Γ(X, ⊤)) :
    ∃ (n : ℕ) (a : Γ(V, ⊤)), g ^ p ^ n = f.appTop a := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hX : (p : Γ(X, ⊤)) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg f.appTop.hom hV
  let πX := X.absoluteWeakNormalizationHom
  let s : Γ(X.absoluteWeakNormalization, ⊤) := πX.appTop g
  have hpull (h : pullback f f ⟶ X) :
      (absoluteWeakNormalizationMap h).appTop s =
        (pullback f f).absoluteWeakNormalizationHom.appTop (h.appTop g) := by
    exact appTop_apply_eq_of_comp_eq (absoluteWeakNormalizationMap_spec h) g
  have hs : (absoluteWeakNormalizationMap (pullback.fst f f)).appTop s =
      (absoluteWeakNormalizationMap (pullback.snd f f)).appTop s := by
    rw [hpull, hpull, ← sub_eq_zero, ← map_sub]
    have _ : IsReduced (pullback f f).absoluteWeakNormalization :=
      isReduced_absoluteWeakNormalization _
    exact IsReduced.eq_zero _ ((isNilpotent_fst_appTop_sub_snd_appTop f g).map _)
  obtain ⟨t, ht, -⟩ := existsUnique_properSurjective_glue_section f s hs
  obtain ⟨n, a, ha⟩ := exists_pow_eq_appTop_absoluteWeakNormalizationHom p hV t
  have hkey : πX.appTop (g ^ p ^ n - f.appTop a) = 0 := by
    rw [map_sub, map_pow, sub_eq_zero]
    show s ^ p ^ n = _
    rw [← ht, ← map_pow, ha]
    exact appTop_apply_eq_of_comp_eq (absoluteWeakNormalizationMap_spec f) a
  have : Surjective πX := surjective_absoluteWeakNormalizationHom X
  obtain ⟨m, hm⟩ := exists_pow_prime_pow_eq_zero_of_appTop_eq_zero p πX _ hkey
  refine ⟨n + m, a ^ p ^ m, ?_⟩
  have hsub : (g ^ p ^ n - f.appTop a) ^ p ^ m = (g ^ p ^ n) ^ p ^ m - (f.appTop a) ^ p ^ m := by
    by_cases hR : Nontrivial Γ(X, ⊤)
    · have : CharP Γ(X, ⊤) p :=
        (CharP.charP_iff_prime_eq_zero (R := Γ(X, ⊤)) (p := p) Fact.out).2 hX
      exact sub_pow_char_pow (g ^ p ^ n) (f.appTop a) m
    · have : Subsingleton Γ(X, ⊤) := not_nontrivial_iff_subsingleton.mp hR
      exact Subsingleton.elim _ _
  rw [hsub, sub_eq_zero, ← pow_mul, ← pow_add] at hm
  rw [hm, map_pow]

end AlgebraicGeometry

end
