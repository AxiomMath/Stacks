module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOverAffineCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDenseAffineFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.IsoClassBound

/-!
# Axiom [-1] of Artin's criterion for `Complexes_{X/B}`

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces over an affine
scheme `S = Spec Λ` of a big fppf site, as in Stacks 0DLE.  This file proves the set-theoretic
condition of Artin's axioms for the category `Complexes_{X/Y}`: there is an object `T` of the
site such that for every object `U = Spec k` of the site of finite type over `S`, with `k` a
field, the isomorphism classes of the fibre of `Complexes_{X/Y}` over `U` are at most as many as
the size of `T`.  The source of Stacks 0DLN omits this condition; it is the hypothesis `hsize` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`.

## The argument

An object of the fibre over `U` is a morphism `g : U ⟶ Y` together with an object `E` of
`D(𝒪_{X_g})` satisfying conditions (1) and (2) of Stacks 0DLD; only the pseudo-coherence of `E`,
the first half of condition (1), is used.

* There are at most `2 ^ max (size S) (size U')` morphisms `g`, `U'` being a fixed atlas of `Y`
  (`AlgebraicGeometry.Space.mk_obj_le_of_atlas`).
* The base change `X_g` is a quasi-compact algebraic space, `f` being proper and `U` affine, so it
  has an affine covering chart (Stacks 03H6), of finite type over `U`, hence of size at most
  `size S`.  Above it the small étale site of `X_g` has a dense family of affine charts bounded
  by `2 ^ size S` (`AlgebraicGeometry.Space.SmallEtale.exists_denseAffineFamily`), and the
  pseudo-coherent objects of `D(𝒪_{X_g})` fall into at most `2 ^ 2 ^ 2 ^ size S` isomorphism
  classes (`AlgebraicGeometry.RingedSite.exists_family_iso_of_isPseudoCoherent`).
* The cutoff of the site is a strong limit, so the product of the two bounds is the size of an
  object of the site over `S`: the spectrum of a polynomial ring over `Λ`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isQuasiCompactSpace_space`: base changes of the
  standing morphism to affine test schemes are quasi-compact.
* `AlgebraicGeometry.Space.ComplexesSituation.size_chartScheme_le`: a quasi-compact chart of such
  a base change is no larger than `S`.
* `AlgebraicGeometry.Space.ComplexesSituation.exists_family_iso_of_isPseudoCoherent_space`: the
  bound on the pseudo-coherent objects of `D(𝒪_{X_T})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe d u z

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base change of the standing morphism to an affine test scheme is quasi-compact**: the
standing morphism is proper, hence quasi-compact, and an affine scheme is quasi-compact. -/
theorem isQuasiCompactSpace_space (D : ComplexesSituation B S hS) (T : SchemesOver D.Y)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)] :
    IsQuasiCompactSpace B S hS (D.space T).1 :=
  isQuasiCompactSpace_pullback_of_isQuasiCompact_pullback_snd B S hS D.f.hom D.X.2 D.Y.2
    (fun Z g => isQuasiCompact_pullback_snd_of_isQuasiCompact B S hS D.proper.2.1.2 Z g)
    T.left T.hom.hom inferInstance

/-- **A quasi-compact chart of the base change to a test scheme is no larger than the test
scheme.**  The chart maps to the test scheme by a morphism locally of finite presentation: the
projection of the base change is locally of finite presentation on every étale chart. -/
theorem size_chartScheme_le (D : ComplexesSituation B S hS) (T : SchemesOver D.Y)
    (U₀ : SmallEtale B S hS (D.space T).1) [CompactSpace (chartScheme U₀)] :
    (chartScheme U₀).size ≤ ((BigFppfOver.toScheme B S hS).obj T.left).size := by
  let h : U₀.obj.left ⟶ T.left :=
    Yoneda.fullyFaithful.preimage (U₀.obj.hom ≫ (D.projection T).hom)
  have hh : yoneda.map h = U₀.obj.hom ≫ (D.projection T).hom := Yoneda.fullyFaithful.map_preimage _
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 T.left)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 T.left)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h) :=
    D.projection_isLocallyOfFinitePresentation T U₀.obj.left T.left U₀.obj.hom
      (yoneda.map (𝟙 T.left)) h U₀.property hid
      (by rw [CategoryTheory.Functor.map_id]; exact (Category.comp_id (yoneda.map h)).trans hh)
  exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h)

/-- **The pseudo-coherent objects of `D(𝒪_{X_T})` are boundedly many**, for an affine test
scheme `T`: at most `2 ^ 2 ^ 2 ^ size T` isomorphism classes, at any model of the derived
category.  The base change `X_T` is quasi-compact, so it has an affine chart covering its small
étale site (Stacks 03H6), no larger than `T`; above it the small étale site has a dense family of
affine charts bounded by `2 ^ size T`, and
`AlgebraicGeometry.RingedSite.exists_family_iso_of_isPseudoCoherent` applies. -/
theorem exists_family_iso_of_isPseudoCoherent_space (D : ComplexesSituation B S hS)
    (T : SchemesOver D.Y) [IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)]
    [hD : HasDerivedCategory.{d} (Modules.{u, u} B S hS (D.space T).1 (D.space T).2)] :
    ∃ (Cd : Type u) (F : Cd → DerivedCategory (Modules.{u, u} B S hS (D.space T).1 (D.space T).2)),
      #Cd ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        ((BigFppfOver.toScheme B S hS).obj T.left).size ∧
      ∀ E, (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).IsPseudoCoherent E →
        ∃ a : Cd, Nonempty (F a ≅ E) := by
  have hqc := D.isQuasiCompactSpace_space T
  obtain ⟨U₀, hU₀, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS _ (D.space T).2 hqc
  have : IsAffine (chartScheme U₀) := hU₀
  have hU₀size := D.size_chartScheme_le T U₀
  obtain ⟨ι, c, hdense, hι, hc⟩ := SmallEtale.exists_denseAffineFamily U₀ hcov
  set σ := ((BigFppfOver.toScheme B S hS).obj T.left).size with hσdef
  have hσ : ℵ₀ ≤ σ := Scheme.aleph0_le_size _
  have hν : ℵ₀ ≤ (2 : Cardinal.{u}) ^ σ := hσ.trans (Cardinal.cantor σ).le
  have hσle : σ ≤ 2 ^ σ := (Cardinal.cantor σ).le
  have hΓ : ∀ i, #Γ(chartScheme (c i), ⊤) ≤ σ := fun i => by
    obtain ⟨haff, f, hf⟩ := hc i
    exact ((chartScheme (c i)).mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans
      ((Scheme.size_le_of_locallyOfFiniteType f).trans hU₀size)
  have hΓ₀ : #Γ(chartScheme U₀, ⊤) ≤ σ :=
    ((chartScheme U₀).mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans hU₀size
  refine RingedSite.exists_family_iso_of_isPseudoCoherent
    (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2) c (hc := hdense) hν ?_ ?_ ?_
  · refine hι.trans ?_
    have : (2 : Cardinal.{u}) ^ max ℵ₀ #Γ(chartScheme U₀, ⊤) ≤ 2 ^ σ :=
      Cardinal.power_le_power_left two_ne_zero (max_le hσ hΓ₀)
    exact (mul_le_mul' hν this).trans (Cardinal.mul_eq_self hν).le
  · intro i j
    have : IsAffine (chartScheme (c j)) := (hc j).1
    refine (Cardinal.mk_le_of_injective
      (SmallEtale.chartSchemeMap_injective (W := c i) (W' := c j))).trans ?_
    refine (Scheme.mk_hom_le_of_isAffine _ _).trans ?_
    calc #Γ(chartScheme (c i), ⊤) ^ #Γ(chartScheme (c j), ⊤) ≤ σ ^ #Γ(chartScheme (c j), ⊤) :=
          Cardinal.power_le_power_right (hΓ i)
      _ ≤ σ ^ σ := Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hσ).ne' (hΓ j)
      _ = 2 ^ σ := Cardinal.power_self_eq hσ
  · intro i
    exact (hΓ i).trans hσle

/-- A test scheme over `Y` with underlying object `U` is determined by its morphism to `Y`, a
point of `Y` with values in `U`. -/
theorem injective_schemesOver_point (Y : AlgebraicSpaces B S hS) (U : BigFppfOver B S hS) :
    Function.Injective (fun T : {T : SchemesOver Y // T.left = U} =>
      Y.1.map (eqToHom (congrArg op T.2)) (yonedaEquiv T.1.hom.hom)) := by
  intro T₁ T₂ h
  obtain ⟨T₁, hT₁⟩ := T₁
  obtain ⟨T₂, hT₂⟩ := T₂
  subst hT₁
  obtain ⟨l₁, r₁, h₁⟩ := T₁
  obtain ⟨l₂, r₂, h₂⟩ := T₂
  change l₂ = l₁ at hT₂
  subst hT₂
  obtain ⟨⟨⟩⟩ := r₁
  obtain ⟨⟨⟩⟩ := r₂
  simp only [eqToHom_refl, Functor.map_id_apply] at h
  obtain rfl : h₁ = h₂ := ObjectProperty.hom_ext _ (yonedaEquiv.injective h)
  rfl

section Fibre

attribute [local instance] complexesCategory

/-- **Two objects of a fibre of `Complexes_{X/Y}` with the same test scheme and isomorphic
complexes are isomorphic**: the identity of the test scheme together with the isomorphism of
complexes, read through `L(X_{𝟙})^* ≅ 𝟭`, is a morphism of the fibre, and the fibres are
groupoids. -/
theorem nonempty_iso_fiber_of_iso (D : ComplexesSituation B S hS) {U : BigFppfOver B S hS}
    {T : SchemesOver D.Y} {E₁ E₂ : derivedModules B S hS (D.space T)}
    (h₁₁ : D.IsRelativelyPerfect T E₁) (h₁₂ : D.HasNoNegativeFibreExt T E₁)
    (h₂₁ : D.IsRelativelyPerfect T E₂) (h₂₂ : D.HasNoNegativeFibreExt T E₂)
    (ha₁ : (complexesFunctor D).obj ⟨T, E₁, h₁₁, h₁₂⟩ = U)
    (ha₂ : (complexesFunctor D).obj ⟨T, E₂, h₂₁, h₂₂⟩ = U) (e : E₁ ≅ E₂) :
    Nonempty (Functor.Fiber.mk ha₁ ≅ Functor.Fiber.mk ha₂) := by
  subst ha₁
  let m : ComplexesHom (⟨T, E₁, h₁₁, h₁₂⟩ : ComplexesObject D) ⟨T, E₂, h₂₁, h₂₂⟩ :=
    { base := 𝟙 T
      fibre := (D.idComparison T).hom.app E₂ ≫ e.inv
      isIso_fibre := inferInstance }
  have hlift : (complexesFunctor D).IsHomLift (𝟙 T.left)
      (m : (⟨T, E₁, h₁₁, h₁₂⟩ : ComplexesObject D) ⟶ ⟨T, E₂, h₂₁, h₂₂⟩) := by
    refine IsHomLift.of_fac (p := complexesFunctor D) _ _ rfl ha₂ ?_
    rw [complexesFunctor_map]
    show 𝟙 T.left = eqToHom (rfl : T.left = T.left) ≫ 𝟙 T.left ≫ eqToHom (rfl : T.left = T.left)
    simp
  have hG := isGroupoid_fiber_complexesFunctor D T.left
  let φ := Functor.Fiber.homMk (complexesFunctor D) T.left
    (m : (⟨T, E₁, h₁₁, h₁₂⟩ : ComplexesObject D) ⟶ ⟨T, E₂, h₂₁, h₂₂⟩)
  exact ⟨@asIso _ _ _ _ φ (hG.all_isIso φ)⟩

/-- **The fibres of `Complexes_{X/Y}` over the spectra of fields are few.**  There is a cardinal
`μ` below the cutoff of the site (the size of an atlas of `Y`) such that the fibre over an object
`U = Spec k` of the site, `k` a field, has at most `2 ^ 2 ^ 2 ^ max (size U) μ` isomorphism
classes. -/
theorem exists_mk_quotient_fiber_le (D : ComplexesSituation B S hS) :
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k], U.left.1 = Spec (.of k) →
        Cardinal.lift.{u, u + 1}
            (Cardinal.mk (Quotient (isIsomorphicSetoid ((complexesFunctor D).Fiber U)))) ≤
          Cardinal.lift.{u + 1, u}
            ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
              max ((BigFppfOver.toScheme B S hS).obj U).size μ) := by
  obtain ⟨U', a, ha_s, ha_e⟩ := D.Y.2.exists_atlas
  refine ⟨((BigFppfOver.toScheme B S hS).obj U').size, U'.left.property, fun U k _ hk => ?_⟩
  set sU := ((BigFppfOver.toScheme B S hS).obj U).size with hsU
  set μ := ((BigFppfOver.toScheme B S hS).obj U').size with hμ
  have e : (BigFppfOver.toScheme B S hS).obj U = Spec (.of k) := hk
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := by rw [e]; infer_instance
  have : Nonempty ((BigFppfOver.toScheme B S hS).obj U) := by rw [e]; infer_instance
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj U) := by rw [e]; infer_instance
  let G := {T : SchemesOver D.Y // T.left = U}
  have hTaff : ∀ T : G, IsAffine ((BigFppfOver.toScheme B S hS).obj T.1.left) := fun T => by
    rw [T.2]
    infer_instance
  -- The model of the derived category is the one `AlgebraicGeometry.Space.derivedModules`
  -- (`StacksFrontier/AlgebraicGeometry/Quot/DerivedPullbackSectionFunctor.lean`) is formed at.
  choose Cd F hCd hF using fun T : G => by
    have := hTaff T
    exact exists_family_iso_of_isPseudoCoherent_space D T.1 (hD := HasDerivedCategory.standard _)
  -- the code of an object of the fibre: its test scheme and the index of its complex
  let code : (complexesFunctor D).Fiber U → Σ T : G, ULift.{u + 1} (Cd T) := fun A =>
    ⟨⟨A.1.T, A.2⟩, ⟨(hF ⟨A.1.T, A.2⟩ A.1.E A.1.relativelyPerfect.1).choose⟩⟩
  have hcode : ∀ A₁ A₂ : (complexesFunctor D).Fiber U, code A₁ = code A₂ → Nonempty (A₁ ≅ A₂) := by
    rintro ⟨⟨T₁, E₁, h₁₁, h₁₂⟩, ha₁⟩ ⟨⟨T₂, E₂, h₂₁, h₂₂⟩, ha₂⟩ h
    obtain ⟨hT, hc⟩ := Sigma.mk.inj_iff.mp h
    have hT' : T₁ = T₂ := congrArg Subtype.val hT
    subst hT'
    have hc' := congrArg ULift.down (eq_of_heq hc)
    obtain ⟨e₁⟩ := (hF ⟨T₁, ha₁⟩ E₁ h₁₁.1).choose_spec
    obtain ⟨e₂⟩ := (hF ⟨T₁, ha₂⟩ E₂ h₂₁.1).choose_spec
    exact nonempty_iso_fiber_of_iso D h₁₁ h₁₂ h₂₁ h₂₂ ha₁ ha₂
      (e₁.symm ≪≫ eqToIso (congrArg (F ⟨T₁, ha₁⟩) hc') ≪≫ e₂)
  have hinj : Function.Injective (fun q : Quotient (isIsomorphicSetoid
      ((complexesFunctor D).Fiber U)) => code q.out) := by
    intro q₁ q₂ h
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    exact Quotient.sound (hcode _ _ h)
  have hY := mk_obj_le_of_atlas D.Y.2 a ha_s ha_e U
  have hG : Cardinal.lift.{u, u + 1} #G ≤ Cardinal.lift.{u + 1, u} #(D.Y.1.obj (op U)) :=
    Cardinal.lift_mk_le_lift_mk_of_injective (injective_schemesOver_point D.Y U)
  rw [Cardinal.lift_id'.{u, u + 1}] at hG
  have hCd' :
      ∀ T : G, #(Cd T) ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ sU :=
    fun T => by simpa only [T.2] using hCd T
  set β : Cardinal.{u} := (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max sU μ
    with hβ
  have hm : ℵ₀ ≤ max sU μ := (Scheme.aleph0_le_size _).trans (le_max_left _ _)
  have hβ₀ : ℵ₀ ≤ β := hm.trans ((Cardinal.cantor _).le.trans ((Cardinal.cantor _).le.trans
    (Cardinal.cantor _).le))
  have h1 : (2 : Cardinal.{u}) ^ max sU μ ≤ β :=
    (Cardinal.cantor _).le.trans (Cardinal.cantor _).le
  have h2 : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ sU ≤ β :=
    Cardinal.power_le_power_left two_ne_zero (Cardinal.power_le_power_left two_ne_zero
      (Cardinal.power_le_power_left two_ne_zero (le_max_left _ _)))
  rw [Cardinal.lift_id'.{u, u + 1}]
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_mk_mul_iSup _).trans ?_
  have hsup : (⨆ T : G, #(ULift.{u + 1} (Cd T))) ≤ Cardinal.lift.{u + 1} β := by
    by_cases hne : Nonempty G
    · refine ciSup_le' (fun T => ?_)
      rw [Cardinal.mk_uLift]
      exact Cardinal.lift_le.2 ((hCd' T).trans h2)
    · have : IsEmpty G := not_nonempty_iff.mp hne
      simp
  calc #G * ⨆ T : G, #(ULift.{u + 1} (Cd T))
      ≤ Cardinal.lift.{u + 1} β * Cardinal.lift.{u + 1} β :=
        mul_le_mul' (hG.trans (Cardinal.lift_le.2 (hY.trans h1))) hsup
    _ = Cardinal.lift.{u + 1} β := by
        rw [← Cardinal.lift_mul, Cardinal.mul_eq_self hβ₀]

/-- **Axiom [-1] of Artin's criterion for `Complexes_{X/Y}` over an affine base.**  For the
standing data of Stacks 0DLE over `S = Spec Λ` there is an object `T` of the site whose size
bounds the number of isomorphism classes of the fibre over every object `Spec k` of the site of
finite type over `S`, `k` a field.  This is exactly the hypothesis `hsize` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`.

The fibres are bounded by `2 ^ 2 ^ 2 ^ max (size S) μ`, `μ` the size of an atlas of `Y`
(`AlgebraicGeometry.Space.ComplexesSituation.exists_mk_quotient_fiber_le`, an object of finite
type over `S` being no larger than `S`), which lies below the cutoff of the site, a strong
limit; the spectrum of a polynomial ring over `Λ` in that many variables is an object of the site
over `S` of at least that size.  If `Λ` is the zero ring there are no objects `Spec k` over
`S` at all. -/
theorem exists_isSizeBounded (Λ : Type u) [CommRing Λ]
    {hΛ : B.Contains (Spec (CommRingCat.of Λ))} (D : ComplexesSituation B _ hΛ) :
    ∃ T : BigFppfOver B _ hΛ,
      ∀ (U : BigFppfOver B _ hΛ) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B _ hΛ U →
        Cardinal.lift.{u, u + 1}
            (Cardinal.mk (Quotient (isIsomorphicSetoid ((complexesFunctor D).Fiber U)))) ≤
          Cardinal.lift.{u + 1, u} T.left.1.size := by
  obtain ⟨μ, hμ, hb⟩ := D.exists_mk_quotient_fiber_le
  set σ := (Spec (CommRingCat.of Λ)).size with hσ
  set β : Cardinal.{u} := (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max σ μ
    with hβ
  have hβlt : β < B.cutoff :=
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit
      (max_lt hΛ hμ)))
  by_cases hΛ0 : Subsingleton Λ
  · refine ⟨Over.mk (𝟙 _), fun U k _ hk _ => ?_⟩
    exfalso
    have : IsEmpty (Spec (CommRingCat.of Λ)) := PrimeSpectrum.isEmpty_iff_subsingleton.2 hΛ0
    obtain ⟨x⟩ : Nonempty U.left.1 := by rw [hk]; infer_instance
    exact (this.false : (Spec (CommRingCat.of Λ) : Type u) → False) ((B.inclusion.map U.hom).base x)
  have : Nontrivial Λ := not_subsingleton_iff_nontrivial.1 hΛ0
  let R := MvPolynomial β.out Λ
  have hΛσ : #Λ ≤ σ := by rw [hσ, Scheme.size_Spec]; exact le_max_right _ _
  have hRle : #R ≤ max ℵ₀ (max β σ) := by
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    rw [Cardinal.mk_out]
    exact max_le (max_le ((hΛσ.trans (le_max_right _ _)).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _))) (le_max_left _ _)
  have hRcont : B.Contains (Spec (CommRingCat.of R)) := by
    show (Spec (CommRingCat.of R)).size < B.cutoff
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff (hRle.trans_lt (max_lt B.aleph0_lt_cutoff (max_lt hβlt hΛ)))
  refine ⟨siteObject B _ hΛ hRcont (Spec.map (CommRingCat.ofHom (algebraMap Λ R))),
    fun U k _ hk hft => ?_⟩
  have : LocallyOfFiniteType (B.inclusion.map U.hom) := hft.1
  have : QuasiCompact (B.inclusion.map U.hom) := hft.2
  have hU : ((BigFppfOver.toScheme B _ hΛ).obj U).size ≤ σ :=
    Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (B.inclusion.map U.hom)
  refine (hb U k hk).trans (Cardinal.lift_le.2 ?_)
  calc (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        max ((BigFppfOver.toScheme B _ hΛ).obj U).size μ ≤ β :=
        Cardinal.power_le_power_left two_ne_zero (Cardinal.power_le_power_left two_ne_zero
          (Cardinal.power_le_power_left two_ne_zero (max_le_max hU le_rfl)))
    _ ≤ #R := by
      rw [← Cardinal.mk_out β]
      exact Cardinal.mk_le_of_injective (MvPolynomial.X_injective (σ := β.out) (R := Λ))
    _ ≤ (Spec (CommRingCat.of R)).size := by
      rw [Scheme.size_Spec]
      exact le_max_right _ _

end Fibre

end AlgebraicGeometry.Space.ComplexesSituation
