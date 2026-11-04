module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Spectra of finite type algebras over an affine object of the big fppf site

Let `Z` be an object of the big fppf category over `S` whose underlying scheme is affine, with
ring of global sections `Γ(Z)`. For a `Γ(Z)`-algebra `R` of finite type, `Spec R` is again an
object of the site, `AlgebraicGeometry.BigFppfOver.specObj Z R`, lying over `Z`. This file gives
the morphisms out of it — to an affine object `X` over `Z`, from a ring map `Γ(X) → R`, and to
another such spectrum, from an algebra map — and reads properties of these morphisms, their
equality, and pullback squares among them on rings: a morphism `specObj Z R ⟶ X` to an affine
object is determined by its ring map `Γ(X) → R` (`AlgebraicGeometry.BigFppfOver.ringOf`), and a
pushout square of rings gives a pullback square of the site and of represented presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace BigFppfOver

/-- A ring map out of a commutative ring, as a morphism of `CommRingCat` to `CommRingCat.of`. -/
def ringHomOf {X : CommRingCat.{u}} {R : Type u} [CommRing R] (χ : X →+* R) :
    X ⟶ CommRingCat.of R :=
  CommRingCat.ofHom χ

/-- The underlying ring map of `ringHomOf χ` is `χ`. -/
@[simp]
theorem ringHomOf_hom {X : CommRingCat.{u}} {R : Type u} [CommRing R] (χ : X →+* R) :
    (ringHomOf χ).hom = χ :=
  rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section QuotientPushout

variable {B' A₀ : CommRingCat.{u}} (π : B' ⟶ A₀) (hπ : Function.Surjective π.hom)
  (S₁ : Type u) [CommRing S₁] [Algebra B' S₁]

/-- The map `A₀ → S₁ ⧸ J S₁` for `π : B' → A₀` surjective with kernel `J`. -/
noncomputable def quotientBaseMap :
    A₀ →+* S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁) :=
  (Ideal.Quotient.lift (RingHom.ker π.hom) ((Ideal.Quotient.mk _).comp (algebraMap B' S₁))
    (fun j hj => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hj)).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

/-- `quotientBaseMap` sends `π b` to the class of the image of `b` in `S₁`. -/
theorem quotientBaseMap_apply (b : B') :
    quotientBaseMap π hπ S₁ (π.hom b) = Ideal.Quotient.mk _ (algebraMap B' S₁ b) := by
  have h : (RingHom.quotientKerEquivOfSurjective hπ).symm (π.hom b) =
      Ideal.Quotient.mk _ b := by
    rw [RingEquiv.symm_apply_eq, RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp only [quotientBaseMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h, Ideal.Quotient.lift_mk]

/-- A ring map `A₀ → S₁ ⧸ J S₁` which is `B' → S₁ ⧸ J S₁` after `π` is `quotientBaseMap`. -/
theorem eq_quotientBaseMap_of_comp (φ : A₀ →+* S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁))
    (hφ : φ.comp π.hom = algebraMap B' (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁))) :
    φ = quotientBaseMap π hπ S₁ := by
  ext z
  obtain ⟨b, rfl⟩ := hπ z
  rw [quotientBaseMap_apply, ← RingHom.comp_apply, hφ, Ideal.Quotient.mk_algebraMap]

variable (h : S₁)

/-- The ring `(S₁ ⧸ J S₁)[1/h]`. -/
abbrev AwayQuotient :=
  Localization.Away (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁)) h)

/-- The map out of `(S₁ ⧸ J S₁)[1/h]` induced by a map out of `S₁[1/h]` killing `J`. -/
noncomputable def awayQuotientDesc {T : Type u} [CommRing T] (p : Localization.Away h →+* T)
    (hp : ∀ j ∈ RingHom.ker π.hom, p (algebraMap B' (Localization.Away h) j) = 0) :
    AwayQuotient π S₁ h →+* T :=
  IsLocalization.Away.lift (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁)) h)
    (g := Ideal.Quotient.lift ((RingHom.ker π.hom).map (algebraMap B' S₁))
      (p.comp (algebraMap S₁ _)) (by
      have hle : (RingHom.ker π.hom).map (algebraMap B' S₁) ≤
          RingHom.ker (p.comp (algebraMap S₁ (Localization.Away h))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro j hj
        simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply]
        exact hp j hj
      exact fun y hy => hle hy))
    (by
      rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
      exact (IsLocalization.Away.algebraMap_isUnit h).map _)

/-- `awayQuotientDesc` sends the image of `s ∈ S₁` to `p` of the image of `s` in `S₁[1/h]`. -/
theorem awayQuotientDesc_algebraMap {T : Type u} [CommRing T] (p : Localization.Away h →+* T)
    (hp : ∀ j ∈ RingHom.ker π.hom, p (algebraMap B' (Localization.Away h) j) = 0) (s : S₁) :
    awayQuotientDesc π S₁ h p hp
      (algebraMap (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) _
        (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁)) s)) =
      p (algebraMap S₁ _ s) := by
  rw [awayQuotientDesc, IsLocalization.Away.lift_eq, Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- The map `S₁[1/h] → (S₁ ⧸ J S₁)[1/h]`, over `B'`. -/
noncomputable def awayQuotientAlgHom :
    Localization.Away h →ₐ[B'] AwayQuotient π S₁ h where
  toRingHom := IsLocalization.Away.map (Localization.Away h) (AwayQuotient π S₁ h)
    (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁))) h
  commutes' b := by
    have h1 : ∀ s : S₁, IsLocalization.Away.map (Localization.Away h) (AwayQuotient π S₁ h)
        (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁))) h
        (algebraMap S₁ (Localization.Away h) s) =
        algebraMap (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) _
          (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁)) s) :=
      fun s => IsLocalization.map_eq _ _
    change IsLocalization.Away.map _ _ _ h (algebraMap _ (Localization.Away h) b) = _
    rw [IsScalarTower.algebraMap_apply B' S₁ (Localization.Away h), h1,
      IsScalarTower.algebraMap_apply B' (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁))
        (AwayQuotient π S₁ h), Ideal.Quotient.mk_algebraMap]

/-- The map `A₀ → (S₁ ⧸ J S₁)[1/h]`. -/
noncomputable def awayQuotientBase : A₀ →+* AwayQuotient π S₁ h :=
  (algebraMap (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) (AwayQuotient π S₁ h)).comp
    (quotientBaseMap π hπ S₁)

/-- The map `A₀ → (S₁ ⧸ J S₁)[1/h]` composed with `π` is the algebra map from `B'`. -/
theorem awayQuotientBase_comp :
    (awayQuotientBase π hπ S₁ h).comp π.hom = algebraMap B' (AwayQuotient π S₁ h) := by
  ext b
  simp only [awayQuotientBase, RingHom.comp_apply, quotientBaseMap_apply]
  rw [IsScalarTower.algebraMap_apply B' (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁))
      (AwayQuotient π S₁ h), Ideal.Quotient.mk_algebraMap]

/-- `awayQuotientBase` sends `π b` to the image of `b` in `(S₁ ⧸ J S₁)[1/h]`. -/
theorem awayQuotientBase_apply (b : B') :
    awayQuotientBase π hπ S₁ h (π.hom b) =
      algebraMap (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) (AwayQuotient π S₁ h)
        (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁)) (algebraMap B' S₁ b)) := by
  simp only [awayQuotientBase, RingHom.comp_apply, quotientBaseMap_apply]

/-- **Localizing commutes with reducing modulo the kernel, as a pushout square.** For
`π : B' → A₀` surjective with kernel `J`, a `B'`-algebra `S₁` and `h ∈ S₁`, the ring
`(S₁ ⧸ J S₁)[1/h]` is the pushout of `S₁[1/h]` and `A₀` over `B'`. -/
theorem isPushout_away_quotient :
    IsPushout (ringHomOf (algebraMap B' (Localization.Away h))) π
      (CommRingCat.ofHom (awayQuotientAlgHom π S₁ h).toRingHom)
      (ringHomOf (awayQuotientBase π hπ S₁ h)) := by
  have ha : ∀ s : S₁, (awayQuotientAlgHom π S₁ h).toRingHom
      (algebraMap S₁ (Localization.Away h) s) =
      algebraMap (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) _
        (Ideal.Quotient.mk ((RingHom.ker π.hom).map (algebraMap B' S₁)) s) :=
    fun s => by
      show IsLocalization.Away.map _ _ _ h _ = _
      exact IsLocalization.map_eq _ _
  have hw : ringHomOf (algebraMap B' (Localization.Away h)) ≫
      CommRingCat.ofHom (awayQuotientAlgHom π S₁ h).toRingHom =
      π ≫ ringHomOf (awayQuotientBase π hπ S₁ h) := by
    ext x
    simp only [CommRingCat.hom_comp, ringHomOf_hom, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [IsScalarTower.algebraMap_apply B' S₁ (Localization.Away h), ha, awayQuotientBase_apply]
  have hcc : ∀ (s : PushoutCocone (ringHomOf (algebraMap B' (Localization.Away h))) π) (y : B'),
      s.inl.hom (algebraMap B' (Localization.Away h) y) = s.inr.hom (π.hom y) := fun s y => by
    have hc := congrArg (fun φ => φ.hom y) s.condition
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, ringHomOf_hom] using hc
  have hcond : ∀ s : PushoutCocone (ringHomOf (algebraMap B' (Localization.Away h))) π,
      ∀ j ∈ RingHom.ker π.hom, s.inl.hom (algebraMap B' (Localization.Away h) j) = 0 := by
    intro s j hj
    rw [hcc, RingHom.mem_ker.mp hj, map_zero]
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (awayQuotientDesc π S₁ h s.inl.hom (hcond s))) ?_ ?_ ?_)
  · intro s
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    ext z
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.comp_apply]
    rw [ha, awayQuotientDesc_algebraMap]
  · intro s
    ext x
    obtain ⟨y, rfl⟩ := hπ x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.comp_apply, ringHomOf_hom, awayQuotientBase_apply]
    rw [awayQuotientDesc_algebraMap, ← IsScalarTower.algebraMap_apply, hcc]
  · intro s m hm _
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk
      ((RingHom.ker π.hom).map (algebraMap B' S₁)) h))
    apply Ideal.Quotient.ringHom_ext
    ext z
    have hz := congrArg (fun φ => φ.hom (algebraMap S₁ (Localization.Away h) z)) hm
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.comp_apply] at hz
    rw [ha] at hz
    simp only [RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [hz, awayQuotientDesc_algebraMap]

section Localized

variable {D : Type u} [CommRing D]
  (lam : D →+* S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁))

/-- The map `D → (S₁ ⧸ J S₁)[1/h]` through a map `λ : D → S₁ ⧸ J S₁`. -/
noncomputable abbrev awayQuotientOf : D →+* AwayQuotient π S₁ h :=
  (algebraMap (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) (AwayQuotient π S₁ h)).comp lam

/-- If `λ ∘ κ` is `quotientBaseMap`, then `awayQuotientOf λ ∘ κ` is `awayQuotientBase`. -/
theorem awayQuotientOf_comp (κ : A₀ →+* D) (hlam : lam.comp κ = quotientBaseMap π hπ S₁) :
    (awayQuotientOf π S₁ h lam).comp κ = awayQuotientBase π hπ S₁ h := by
  rw [awayQuotientOf, RingHom.comp_assoc, hlam]
  rfl

/-- If `λ ∘ κ` is `quotientBaseMap`, then `awayQuotientOf λ ∘ κ ∘ π` is the algebra map from
`B'`. -/
theorem awayQuotientOf_comp_comp (κ : A₀ →+* D) (hlam : lam.comp κ = quotientBaseMap π hπ S₁) :
    ((awayQuotientOf π S₁ h lam).comp κ).comp π.hom = algebraMap B' (AwayQuotient π S₁ h) := by
  rw [awayQuotientOf_comp π hπ S₁ h lam κ hlam, awayQuotientBase_comp]

/-- If `λ` exhibits `S₁ ⧸ J S₁` as the localization of `D` away from `d`, then
`awayQuotientOf λ : D → (S₁ ⧸ J S₁)[1/h]` is étale. -/
theorem etale_awayQuotientOf (d : D)
    (hloc : @IsLocalization.Away D _ d (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) _
      lam.toAlgebra) :
    (awayQuotientOf π S₁ h lam).Etale := by
  let := lam.toAlgebra
  refine RingHom.Etale.stableUnderComposition _ _ ?_ ?_
  · exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway d)
  · exact RingHom.etale_algebraMap.mpr inferInstance

/-- If `λ` exhibits `S₁ ⧸ J S₁` as the localization of `D` away from `d`, then every prime `𝔭`
of `D` with `d ∉ 𝔭` and `h ∉ λ(𝔭)` is the preimage of a prime of `(S₁ ⧸ J S₁)[1/h]`. -/
theorem exists_isPrime_comap_awayQuotientOf (d : D)
    (hloc : @IsLocalization.Away D _ d (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) _
      lam.toAlgebra) (𝔭 : Ideal D) [𝔭.IsPrime] (hd : d ∉ 𝔭)
    (hh : Ideal.Quotient.mk _ h ∉ 𝔭.map lam) :
    ∃ q : Ideal (AwayQuotient π S₁ h), q.IsPrime ∧ q.comap (awayQuotientOf π S₁ h lam) = 𝔭 := by
  let := lam.toAlgebra
  have := hloc
  have hdisj : Disjoint (Submonoid.powers d : Set D) ↑𝔭 :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime d).mpr hd
  have h𝔵' : (𝔭.map lam).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers d) _ 𝔭 inferInstance hdisj
  have hcomap : (𝔭.map lam).comap lam = 𝔭 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers d) _ inferInstance hdisj
  have hdisj' : Disjoint (Submonoid.powers (Ideal.Quotient.mk
      ((RingHom.ker π.hom).map (algebraMap B' S₁)) h) :
        Set (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁))) ↑(𝔭.map lam) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hh
  refine ⟨(𝔭.map lam).map (algebraMap _ (AwayQuotient π S₁ h)),
    IsLocalization.isPrime_of_isPrime_disjoint _ _ _ h𝔵' hdisj', ?_⟩
  have hqc : ((𝔭.map lam).map (algebraMap _ (AwayQuotient π S₁ h))).comap
      (algebraMap (S₁ ⧸ (RingHom.ker π.hom).map (algebraMap B' S₁)) (AwayQuotient π S₁ h)) =
      𝔭.map lam :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ h𝔵' hdisj'
  rw [awayQuotientOf, ← Ideal.comap_comap, hqc, hcomap]

end Localized

end QuotientPushout


/-- **The spectrum of a finite type algebra over an affine object is an object of the site.** -/
theorem contains_Spec_of_finiteType (Z : BigFppfOver B S hS)
    [IsAffine ((toScheme B S hS).obj Z)] (R : Type u) [CommRing R]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R]
    [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R] :
    B.Contains (Spec (CommRingCat.of R)) := by
  let f : Spec (CommRingCat.of R) ⟶ (toScheme B S hS).obj Z :=
    Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
      ((toScheme B S hS).obj Z).isoSpec.inv
  have : LocallyOfFiniteType (Spec.map
      (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R))) :=
    HasRingHomProperty.Spec_iff.mpr (by
      rw [ringHomOf_hom]; exact RingHom.finiteType_algebraMap.mpr inferInstance)
  have : LocallyOfFiniteType f := inferInstance
  have hcov : (⨆ _ : ULift.{u} Unit,
      (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of R)).affineOpens).1) = ⊤ := by
    ext x; simp
  have hI : Cardinal.mk (ULift.{u} Unit) ≤
      ((toScheme B S hS).obj Z).size ^ Cardinal.aleph0 :=
    calc
      Cardinal.mk (ULift.{u} Unit) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      _ ≤ ((toScheme B S hS).obj Z).size := Scheme.aleph0_le_size _
      _ ≤ ((toScheme B S hS).obj Z).size ^ Cardinal.aleph0 :=
        Cardinal.self_le_power _ (by simp)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_affineCover B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit f (fun _ => ⟨⊤, isAffineOpen_top _⟩) hcov hI Z.left.property

variable (Z : BigFppfOver B S hS) [IsAffine ((toScheme B S hS).obj Z)]
  (R : Type u) [CommRing R] [Algebra Γ((toScheme B S hS).obj Z, ⊤) R]
  [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R]

/-- **`Spec R` over an affine object `Z`, for a finite type `Γ(Z)`-algebra `R`.** -/
noncomputable def specObj : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_Spec_of_finiteType Z R)
    (Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
      ((toScheme B S hS).obj Z).isoSpec.inv ≫
      B.inclusion.map Z.hom)

/-- The underlying scheme of `specObj Z R` is affine. -/
instance : IsAffine ((toScheme B S hS).obj (specObj Z R)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))

/-- The structure morphism `specObj Z R ⟶ Z`. -/
noncomputable def specObjToBase : specObj Z R ⟶ Z :=
  homOfCompEq B S hS
    (Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
      ((toScheme B S hS).obj Z).isoSpec.inv)
    (Category.assoc (Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)))
      ((toScheme B S hS).obj Z).isoSpec.inv (B.inclusion.map Z.hom))

/-- The underlying morphism of schemes of `specObjToBase Z R` is `Spec R → Spec Γ(Z) ≅ Z`. -/
theorem toScheme_map_specObjToBase :
    (toScheme B S hS).map (specObjToBase Z R) =
      Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
        ((toScheme B S hS).obj Z).isoSpec.inv :=
  toScheme_map_homOfCompEq B S hS _ _

variable {Z R}

/-- **The morphism to an affine object over `Z` given by a ring map.** -/
noncomputable def specObjHom {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    (u : X ⟶ Z) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) :
    specObj Z R ⟶ X :=
  homOfCompEq B S hS (Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv)
    (by
      have hw : B.inclusion.map X.hom = (toScheme B S hS).map u ≫ B.inclusion.map Z.hom := by
        rw [← Over.w u]; rfl
      have hc : ((toScheme B S hS).map u).appTop ≫ ringHomOf χ =
          ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) := by
        ext1; rw [CommRingCat.hom_comp, ringHomOf_hom, ringHomOf_hom]; exact h
      have key : (Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv) ≫
          (toScheme B S hS).map u ≫ B.inclusion.map Z.hom =
          Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
            ((toScheme B S hS).obj Z).isoSpec.inv ≫
            B.inclusion.map Z.hom := by
        rw [Category.assoc, ← Category.assoc ((toScheme B S hS).obj X).isoSpec.inv,
          ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
          hc, Category.assoc]
      rw [hw]
      exact key)

/-- The underlying morphism of schemes of `specObjHom u χ h` is `Spec R → Spec Γ(X) ≅ X`. -/
theorem toScheme_map_specObjHom {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    (u : X ⟶ Z) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) :
    (toScheme B S hS).map (specObjHom u χ h) =
      Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv :=
  toScheme_map_homOfCompEq B S hS _ _

/-- **The morphism to an affine object given by a ring map, over a common affine object.** For
affine objects `X` and `Z'` with morphisms `u : X ⟶ Z'` and `v : Z ⟶ Z'`, a ring map
`χ : Γ(X) → R` compatible with `u` and `v` gives a morphism `specObj Z R ⟶ X`. -/
noncomputable def specObjHomOver {X Z' : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    [IsAffine ((toScheme B S hS).obj Z')] (u : X ⟶ Z') (v : Z ⟶ Z')
    (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R).comp ((toScheme B S hS).map v).appTop.hom) :
    specObj Z R ⟶ X :=
  homOfCompEq B S hS (Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv)
    (by
      have hw : B.inclusion.map X.hom = (toScheme B S hS).map u ≫ B.inclusion.map Z'.hom := by
        rw [← Over.w u]; rfl
      have hwZ : B.inclusion.map Z.hom = (toScheme B S hS).map v ≫ B.inclusion.map Z'.hom := by
        rw [← Over.w v]; rfl
      have hc : ((toScheme B S hS).map u).appTop ≫ ringHomOf χ =
          ((toScheme B S hS).map v).appTop ≫
            ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) := by
        ext1; rw [CommRingCat.hom_comp, CommRingCat.hom_comp, ringHomOf_hom, ringHomOf_hom]
        exact h
      have key : (Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv) ≫
          (toScheme B S hS).map u ≫ B.inclusion.map Z'.hom =
          Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
            ((toScheme B S hS).obj Z).isoSpec.inv ≫ (toScheme B S hS).map v ≫
              B.inclusion.map Z'.hom := by
        rw [Category.assoc, ← Category.assoc ((toScheme B S hS).obj X).isoSpec.inv,
          ← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
          hc, Spec.map_comp, Category.assoc, Category.assoc, Scheme.isoSpec_inv_naturality_assoc]
      have key2 : Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
          ((toScheme B S hS).obj Z).isoSpec.inv ≫ B.inclusion.map Z.hom =
          Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)) ≫
            ((toScheme B S hS).obj Z).isoSpec.inv ≫ (toScheme B S hS).map v ≫
              B.inclusion.map Z'.hom := by
        rw [hwZ]
      rw [hw]
      exact key.trans key2.symm)

/-- The underlying morphism of schemes of `specObjHomOver u v χ h` is
`Spec R → Spec Γ(X) ≅ X`. -/
theorem toScheme_map_specObjHomOver {X Z' : BigFppfOver B S hS}
    [IsAffine ((toScheme B S hS).obj X)] [IsAffine ((toScheme B S hS).obj Z')] (u : X ⟶ Z')
    (v : Z ⟶ Z') (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R).comp ((toScheme B S hS).map v).appTop.hom) :
    (toScheme B S hS).map (specObjHomOver u v χ h) =
      Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv :=
  toScheme_map_homOfCompEq B S hS _ _

/-- **The morphism between two spectra over `Z` given by an algebra map.** -/
noncomputable def specObjMap {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₁] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₁]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₂] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₂]
    (ω : R₂ →ₐ[Γ((toScheme B S hS).obj Z, ⊤)] R₁) : specObj Z R₁ ⟶ specObj Z R₂ :=
  homOfCompEq B S hS (Spec.map (CommRingCat.ofHom ω.toRingHom)) (by
    have hc : ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₂) ≫
        CommRingCat.ofHom ω.toRingHom =
          ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₁) := by
      ext1; rw [CommRingCat.hom_comp, ringHomOf_hom, ringHomOf_hom]; exact ω.comp_algebraMap
    have key : Spec.map (CommRingCat.ofHom ω.toRingHom) ≫
        (Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₂)) ≫
          ((toScheme B S hS).obj Z).isoSpec.inv ≫ B.inclusion.map Z.hom) =
        Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₁)) ≫
          ((toScheme B S hS).obj Z).isoSpec.inv ≫ B.inclusion.map Z.hom := by
      rw [← Category.assoc, ← Spec.map_comp, hc]
    exact key)

/-- The underlying morphism of schemes of `specObjMap ω` is `Spec ω`. -/
theorem toScheme_map_specObjMap {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₁] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₁]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₂] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₂]
    (ω : R₂ →ₐ[Γ((toScheme B S hS).obj Z, ⊤)] R₁) :
    (toScheme B S hS).map (specObjMap ω) = Spec.map (CommRingCat.ofHom ω.toRingHom) :=
  toScheme_map_homOfCompEq B S hS _ _

variable (Z R) in
/-- The global sections of `specObj Z R` are `R`. -/
noncomputable def specObjΓIso :
    Γ((toScheme B S hS).obj (specObj Z R), ⊤) ≅ CommRingCat.of R :=
  Scheme.ΓSpecIso (CommRingCat.of R)

/-- **The ring map of a morphism out of `specObj Z R` to an affine object.** -/
noncomputable def ringOf {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    (f : specObj Z R ⟶ X) : Γ((toScheme B S hS).obj X, ⊤) →+* R :=
  (((toScheme B S hS).map f).appTop ≫ (specObjΓIso Z R).hom).hom

/-- On global sections, `Spec φ ≫ X.isoSpec.inv` followed by `ΓSpecIso` is `φ`. -/
private theorem appTop_spec_map_isoSpec_inv {X : Scheme.{u}} [IsAffine X] {A : CommRingCat.{u}}
    (φ : Γ(X, ⊤) ⟶ A) :
    (Spec.map φ ≫ X.isoSpec.inv).appTop ≫ (Scheme.ΓSpecIso A).hom = φ := by
  rw [Scheme.Hom.comp_appTop, Stacks.RelativeSpec.isoSpec_inv_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- On global sections, `specObjHom u χ h` is `χ`. -/
theorem appTop_specObjHom {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    (u : X ⟶ Z) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) :
    ((toScheme B S hS).map (specObjHom u χ h)).appTop ≫ (specObjΓIso Z R).hom =
      ringHomOf χ := by
  rw [toScheme_map_specObjHom]
  exact appTop_spec_map_isoSpec_inv _

/-- The ring map of `specObjHomOver u v χ h` is `χ`. -/
theorem ringOf_specObjHomOver {X Z' : BigFppfOver B S hS}
    [IsAffine ((toScheme B S hS).obj X)] [IsAffine ((toScheme B S hS).obj Z')] (u : X ⟶ Z')
    (v : Z ⟶ Z') (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R).comp ((toScheme B S hS).map v).appTop.hom) :
    ringOf (specObjHomOver u v χ h) = χ := by
  have e : ((toScheme B S hS).map (specObjHomOver u v χ h)).appTop ≫ (specObjΓIso Z R).hom =
      ringHomOf χ := by
    rw [toScheme_map_specObjHomOver]
    exact appTop_spec_map_isoSpec_inv _
  rw [ringOf, e, ringHomOf_hom]

/-- The ring map of `specObjHom u χ h` is `χ`. -/
theorem ringOf_specObjHom {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    (u : X ⟶ Z) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) :
    ringOf (specObjHom u χ h) = χ := by
  rw [ringOf, appTop_specObjHom, ringHomOf_hom]

/-- On global sections, `specObjToBase Z R` is the algebra map `Γ(Z) → R`. -/
theorem appTop_specObjToBase :
    ((toScheme B S hS).map (specObjToBase Z R)).appTop ≫ (specObjΓIso Z R).hom =
      ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) := by
  rw [toScheme_map_specObjToBase]
  exact appTop_spec_map_isoSpec_inv _

/-- The ring map of `specObjToBase Z R` is the algebra map `Γ(Z) → R`. -/
theorem ringOf_specObjToBase :
    ringOf (specObjToBase Z R) = algebraMap Γ((toScheme B S hS).obj Z, ⊤) R := by
  rw [ringOf, appTop_specObjToBase, ringHomOf_hom]

/-- The ring map of `f ≫ k` is the ring map of `f` composed with `k` on global sections. -/
theorem ringOf_comp {X X' : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    [IsAffine ((toScheme B S hS).obj X')] (f : specObj Z R ⟶ X) (k : X ⟶ X') :
    ringOf (f ≫ k) = (ringOf f).comp ((toScheme B S hS).map k).appTop.hom := by
  rw [ringOf, ringOf, Functor.map_comp, Scheme.Hom.comp_appTop, Category.assoc]
  rfl

/-- On global sections, `specObjMap ω` is `ω`. -/
theorem appTop_specObjMap {R₂ : Type u} [CommRing R₂]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₂] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₂]
    (ω : R₂ →ₐ[Γ((toScheme B S hS).obj Z, ⊤)] R) :
    ((toScheme B S hS).map (specObjMap ω)).appTop ≫ (specObjΓIso Z R).hom =
      (specObjΓIso Z R₂).hom ≫ CommRingCat.ofHom ω.toRingHom := by
  rw [toScheme_map_specObjMap]
  exact Scheme.ΓSpecIso_naturality _

/-- The ring map of `specObjMap ω ≫ g` is `ω` composed with the ring map of `g`. -/
theorem ringOf_specObjMap_comp {R₂ : Type u} [CommRing R₂]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₂] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₂]
    (ω : R₂ →ₐ[Γ((toScheme B S hS).obj Z, ⊤)] R) {X : BigFppfOver B S hS}
    [IsAffine ((toScheme B S hS).obj X)] (g : specObj Z R₂ ⟶ X) :
    ringOf (specObjMap ω ≫ g) = ω.toRingHom.comp (ringOf g) := by
  rw [ringOf, ringOf, Functor.map_comp, Scheme.Hom.comp_appTop, Category.assoc,
    appTop_specObjMap, ← Category.assoc]
  rfl

/-- **A morphism out of `specObj Z R` to an affine object is determined by its ring map.** -/
theorem hom_ext_of_ringOf {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    {f g : specObj Z R ⟶ X} (h : ringOf f = ringOf g) : f = g := by
  apply (toScheme B S hS).map_injective
  apply ext_of_isAffine
  have h' : ((toScheme B S hS).map f).appTop ≫ (specObjΓIso Z R).hom =
      ((toScheme B S hS).map g).appTop ≫ (specObjΓIso Z R).hom :=
    CommRingCat.hom_ext h
  exact (cancel_mono _).mp h'

/-- **Properties of a morphism out of `specObj Z R`, read on its ring map.** -/
theorem prop_iff_ringOf (P : MorphismProperty Scheme.{u}) {Q : ∀ {R S : Type u} [CommRing R]
    [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q] {X : BigFppfOver B S hS}
    [IsAffine ((toScheme B S hS).obj X)] (f : specObj Z R ⟶ X) :
    P ((toScheme B S hS).map f) ↔ Q (ringOf f) := by
  rw [HasRingHomProperty.iff_of_isAffine (P := P), ringOf, CommRingCat.hom_comp,
    ((HasRingHomProperty.isLocal_ringHomProperty P).respectsIso).cancel_right_isIso]

/-- **Properties of a morphism between two spectra over `Z`, read on its algebra map.** -/
theorem prop_specObjMap_iff (P : MorphismProperty Scheme.{u}) {Q : ∀ {R S : Type u} [CommRing R]
    [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q] {R₂ : Type u} [CommRing R₂]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₂] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₂]
    (ω : R₂ →ₐ[Γ((toScheme B S hS).obj Z, ⊤)] R) :
    P ((toScheme B S hS).map (specObjMap ω)) ↔ Q ω.toRingHom := by
  rw [toScheme_map_specObjMap]
  exact HasRingHomProperty.Spec_iff

/-- **Properties of `specObjHom`, read on its ring map.** -/
theorem prop_specObjHom_iff (P : MorphismProperty Scheme.{u}) {Q : ∀ {R S : Type u} [CommRing R]
    [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q] {X : BigFppfOver B S hS}
    [IsAffine ((toScheme B S hS).obj X)] (u : X ⟶ Z) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R) :
    P ((toScheme B S hS).map (specObjHom u χ h)) ↔ Q χ := by
  rw [prop_iff_ringOf P, ringOf_specObjHom]

/-- **Composites of `specObjHom`.** -/
theorem specObjHom_comp_eq {X X' : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    [IsAffine ((toScheme B S hS).obj X')] (u : X ⟶ Z) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)
    (k : X ⟶ X') (u' : X' ⟶ Z) (χ' : Γ((toScheme B S hS).obj X', ⊤) →+* R)
    (h' : χ'.comp ((toScheme B S hS).map u').appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)
    (hk : χ.comp ((toScheme B S hS).map k).appTop.hom = χ') :
    specObjHom u χ h ≫ k = specObjHom u' χ' h' :=
  hom_ext_of_ringOf (by rw [ringOf_comp, ringOf_specObjHom, ringOf_specObjHom, hk])

/-- **A prime over the prime of a point gives a point of `specObj` over it.** -/
theorem mem_range_specObjHom {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    (u : X ⟶ Z) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R)
    (y : (toScheme B S hS).obj X) (q : Ideal R) [q.IsPrime]
    (hq : q.comap χ = (((toScheme B S hS).obj X).isoSpec.hom y).asIdeal) :
    y ∈ Set.range ((toScheme B S hS).map (specObjHom u χ h)) := by
  let z : Spec (CommRingCat.of R) := (⟨q, inferInstance⟩ : PrimeSpectrum R)
  refine ⟨z, ?_⟩
  have hq' : (Spec.map (ringHomOf χ)) z = ((toScheme B S hS).obj X).isoSpec.hom y := by
    rw [Spec.map_apply]
    exact PrimeSpectrum.ext hq
  have key : (Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv) z = y := by
    rw [Scheme.Hom.comp_apply, hq', ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [toScheme_map_specObjHom]
  exact key

/-- **A pushout square of rings gives a pullback square of the site.** Let `X` be an affine
object over `Z` through `u`, let `R₁ → R₂` be an algebra map of finite type `Γ(Z)`-algebras and
`χ : Γ(X) → R₂` a ring map over `Γ(Z)`, forming a pushout square of rings with
`Γ(Z) → R₁` and `u`. Then `specObj Z R₂` is the fibre product of `specObj Z R₁` and `X` over
`Z`. -/
theorem isPullback_of_isPushout {X : BigFppfOver B S hS} [IsAffine ((toScheme B S hS).obj X)]
    (u : X ⟶ Z) {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₁] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₁]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₂] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₂]
    (ω : R₁ →ₐ[Γ((toScheme B S hS).obj Z, ⊤)] R₂) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R₂)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₂)
    (hpo : IsPushout (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₁))
      ((toScheme B S hS).map u).appTop (CommRingCat.ofHom ω.toRingHom) (ringHomOf χ)) :
    IsPullback (specObjMap ω) (specObjHom u χ h) (specObjToBase Z R₁) u := by
  have hsch := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have hspec : IsPullback (Spec.map (CommRingCat.ofHom ω.toRingHom))
      (Spec.map (ringHomOf χ) ≫ ((toScheme B S hS).obj X).isoSpec.inv)
      (Spec.map (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₁)) ≫
        ((toScheme B S hS).obj Z).isoSpec.inv)
      ((toScheme B S hS).map u) :=
    hsch.of_iso (Iso.refl _) (Iso.refl _) ((toScheme B S hS).obj X).isoSpec.symm
      ((toScheme B S hS).obj Z).isoSpec.symm (by simp) (by simp) (by simp)
      (by rw [Iso.symm_hom, Iso.symm_hom]; exact Scheme.isoSpec_inv_naturality _)
  have hsch' : IsPullback ((toScheme B S hS).map (specObjMap ω))
      ((toScheme B S hS).map (specObjHom u χ h)) ((toScheme B S hS).map (specObjToBase Z R₁))
      ((toScheme B S hS).map u) := by
    rw [toScheme_map_specObjMap, toScheme_map_specObjHom, toScheme_map_specObjToBase]
    exact hspec
  have : ReflectsLimit (cospan (specObjToBase Z R₁) u) (toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (toScheme B S hS) hsch'

/-- The pullback square of `AlgebraicGeometry.BigFppfOver.isPullback_of_isPushout`, on
represented presheaves. -/
theorem isPullback_yoneda_of_isPushout {X : BigFppfOver B S hS}
    [IsAffine ((toScheme B S hS).obj X)]
    (u : X ⟶ Z) {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₁] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₁]
    [Algebra Γ((toScheme B S hS).obj Z, ⊤) R₂] [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) R₂]
    (ω : R₁ →ₐ[Γ((toScheme B S hS).obj Z, ⊤)] R₂) (χ : Γ((toScheme B S hS).obj X, ⊤) →+* R₂)
    (h : χ.comp ((toScheme B S hS).map u).appTop.hom =
      algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₂)
    (hpo : IsPushout (ringHomOf (algebraMap Γ((toScheme B S hS).obj Z, ⊤) R₁))
      ((toScheme B S hS).map u).appTop (CommRingCat.ofHom ω.toRingHom) (ringHomOf χ)) :
    IsPullback (yoneda.map (specObjMap ω)) (yoneda.map (specObjHom u χ h))
      (yoneda.map (specObjToBase Z R₁)) (yoneda.map u) :=
  (isPullback_of_isPushout u ω χ h hpo).map yoneda

/-- **`Spec (S₁ ⧸ J S₁)[1/h]` is `Spec S₁[1/h] ×_Z X`**, for a closed immersion `u : X ⟶ Z` of
affine objects with ideal `J`. -/
theorem isPullback_yoneda_awayQuotient {X : BigFppfOver B S hS}
    [IsAffine ((toScheme B S hS).obj X)] (u : X ⟶ Z)
    (hπ : Function.Surjective ((toScheme B S hS).map u).appTop.hom)
    (S₁ : Type u) [CommRing S₁] [Algebra Γ((toScheme B S hS).obj Z, ⊤) S₁]
    [Algebra.FiniteType Γ((toScheme B S hS).obj Z, ⊤) S₁] (h : S₁) :
    IsPullback (yoneda.map (specObjMap (awayQuotientAlgHom ((toScheme B S hS).map u).appTop S₁ h)))
      (yoneda.map (specObjHom u (awayQuotientBase ((toScheme B S hS).map u).appTop hπ S₁ h)
        (awayQuotientBase_comp ((toScheme B S hS).map u).appTop hπ S₁ h)))
      (yoneda.map (specObjToBase Z (Localization.Away h))) (yoneda.map u) :=
  isPullback_yoneda_of_isPushout u _ _ _
    (isPushout_away_quotient ((toScheme B S hS).map u).appTop hπ S₁ h)

end BigFppfOver

end AlgebraicGeometry

end
