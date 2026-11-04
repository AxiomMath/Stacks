module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Scheme.AffinePullbackGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.AffineOfEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.ChartIsoAlongThinChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.ChartLevels
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.LocalizedQuotientEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.SpecOverAffineBase

/-!
# An algebraic space over an affine base is represented once a presentation of a thin chart lifts

This is the presentation step of the proof of Stacks 07SQ, in the form it takes over an affine
base `T` with ring of functions `A`.  Let `X` be an algebraic space over `T`, with a surjective
étale affine chart `W` and kernel pair `R ⇉ W`, and let `x₀ : h_{O₀} ⟶ X` be a surjective
morphism out of an affine object, with `W₀ = W ×_X O₀`.  The ring map `C₀ = Γ(O₀) ⟶ Γ(W₀) = D₀`
is étale, so it has a submersive presentation `P₀`, with relations `g₀ⱼ ∈ C₀[x_τ]`.

Suppose that the coefficients of the relations are values `c ↦ coef c` of a finite family, that
`g : σ → A[y_F][x_τ]` specializes to the relations under `y_c ↦ coef c`, and that

* the coefficients lift to functions `θ (y_c)` on `W` which are invariant under the kernel pair
  and restrict to `coef c` on `W₀`;
* the localized quotient `P' = (A[y_F][x_τ]/(g))_Δ` maps to `Γ(W)` over `θ`, sending the
  variables to lifts of the generators of `P₀`.

Then `X` is represented by a scheme.  The proof: `θ` descends to `φ : X ⟶ Spec A[y_F]`, the map
of `P'` gives `β : W ⟶ Spec P'` lifting `φ` on the chart, `Spec P' ⟶ Spec A[y_F]` is étale,
and on the thin chart `W₀` the comparison `W₀ ⟶ O₀ ×_{Spec A[y_F]} Spec P'` is the spectrum of
the isomorphism `C₀ ⊗ P' ≅ D₀` of `Algebra.LocalizedQuotient.bijective_tensorLift`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_of_presentationLift`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial TensorProduct

universe u

namespace AlgebraicGeometry

/-- A morphism from an affine scheme to a spectrum is the spectrum of its ring map. -/
theorem eq_isoSpec_hom_comp_Spec_map {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) :
    f = X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) := by
  have h := Scheme.isoSpec_hom_naturality f
  rw [Scheme.isoSpec_Spec_hom] at h
  rw [Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

/-- A morphism of affine schemes inducing an isomorphism on global functions is an
isomorphism. -/
theorem isIso_of_isAffine_of_isIso_appTop' {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (h : IsIso f.appTop) : IsIso f := by
  have e : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [e]
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme isomorphic to an object of the site, inside it: `Spec Γ(T)` for an affine `T`. -/
theorem contains_spec_affineBaseRing (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    B.Contains (Spec (affineBaseRing B S hS T)) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
    ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv) T.left.property

/-- The spectrum of a polynomial ring in finitely many variables over the functions of an
affine object of the site lies in the site. -/
theorem contains_spec_mvPolynomial (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (F : Type) [Finite F] :
    B.Contains (Spec (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (affineBaseRing B S hS T) _ (contains_spec_affineBaseRing B S hS T)

/-- The spectrum of a finite type algebra over a ring whose spectrum lies in the site lies in
the site. -/
theorem contains_spec_of_finiteType {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    [Algebra.FiniteType R R'] (h : B.Contains (Spec (CommRingCat.of R))) :
    B.Contains (Spec (CommRingCat.of R')) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R R' h

/-- **A morphism into a fibre product of affine objects of the site is an isomorphism** if its
source is affine and its two components exhibit the global functions of its source as the
pushout of the global functions of the factors. -/
theorem isIso_of_isPushout_appTop {O Y Y' V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj O)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (a : O ⟶ Y) (b : Y' ⟶ Y)
    (κ : V ⟶ pullback a b)
    (h : IsPushout ((BigFppfOver.toScheme B S hS).map a).appTop
      ((BigFppfOver.toScheme B S hS).map b).appTop
      ((BigFppfOver.toScheme B S hS).map (κ ≫ pullback.fst a b)).appTop
      ((BigFppfOver.toScheme B S hS).map (κ ≫ pullback.snd a b)).appTop) : IsIso κ := by
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have hsch := (IsPullback.of_hasPullback a b).map (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback a b)) := .of_isPullback hsch
  have h1 := isPushout_appTop_of_isPullback hsch
  have happ : ((BigFppfOver.toScheme B S hS).map κ).appTop = (h1.isoIsPushout _ _ h).hom := by
    apply h1.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom, ← Scheme.Hom.comp_appTop, ← Functor.map_comp]
    · rw [IsPushout.inr_isoIsPushout_hom, ← Scheme.Hom.comp_appTop, ← Functor.map_comp]
  have : IsIso ((BigFppfOver.toScheme B S hS).map κ).appTop := by
    rw [happ]
    infer_instance
  have : IsIso ((BigFppfOver.toScheme B S hS).map κ) :=
    isIso_of_isAffine_of_isIso_appTop' _ inferInstance
  exact isIso_of_reflects_iso κ (BigFppfOver.toScheme B S hS)

section Lift

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (ρ : X ⟶ yoneda.obj T)
  {W R : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
  (w : yoneda.obj W ⟶ X)
  (hws : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
  (hwe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
  {s t : R ⟶ W} (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
  {O₀ W₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj O₀)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]
  (x₀ : yoneda.obj O₀ ⟶ X) (hx₀ : IsSurjective B S hS x₀) (ι₀ : W₀ ⟶ W) (c₀ : W₀ ⟶ O₀)
  (hsq₀ : IsPullback (yoneda.map ι₀) (yoneda.map c₀) w x₀)
  {τ σ : Type} [Finite τ] [Finite σ]
  [Algebra Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤) Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤)]
  (hc₀ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) =
    ((BigFppfOver.toScheme B S hS).map c₀).appTop.hom)
  (P₀ : Algebra.SubmersivePresentation Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) τ σ)
  (hcard : Nat.card τ = Nat.card σ) (m : σ → τ) (hm : Function.Injective m) (hmap : P₀.map = m)
  {F : Type} [Finite F] (coef : F → Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤))
  (g : σ → MvPolynomial τ (MvPolynomial F (affineBaseRing B S hS T)))

/-- The specialization `A[y_F] ⟶ C₀`, `y_c ↦ coef c`. -/
def coefSpecialization : MvPolynomial F (affineBaseRing B S hS T) →+*
    Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤) :=
  eval₂Hom ((BigFppfOver.toScheme B S hS).map (levelChartBase ρ x₀)).appTop.hom coef

include hX hws hwe hR hx₀ hsq₀ hc₀ hcard hmap in
/-- **The presentation step.**  If the coefficients of a submersive presentation of the thin
chart lift to invariant functions on the chart, and the generators lift compatibly to roots of
the lifted relations, then `X` is represented by a scheme. -/
theorem exists_iso_yoneda_of_presentationLift
    (hrel : ∀ j, (g j).map (coefSpecialization B S hS ρ x₀ coef) = P₀.relation j)
    (θ : MvPolynomial F (affineBaseRing B S hS T) →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hθA : θ.comp (algebraMap _ _) =
      ((BigFppfOver.toScheme B S hS).map (levelChartBase ρ w)).appTop.hom)
    (hθinv : ((BigFppfOver.toScheme B S hS).map s).appTop.hom.comp θ =
      ((BigFppfOver.toScheme B S hS).map t).appTop.hom.comp θ)
    (hθ₀ : ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom.comp θ =
      (algebraMap _ _).comp (coefSpecialization B S hS ρ x₀ coef))
    (θ' : Algebra.LocalizedQuotient.ring g m hm →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hθ' : θ'.comp (algebraMap _ _) = θ)
    (hθ'₀ : ∀ i, ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom
      (θ' (algebraMap (Algebra.LocalizedQuotient.quot g) _
        (Ideal.Quotient.mk _ (MvPolynomial.X i)))) =
        P₀.val i) :
    ∃ Z : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj Z) := by
  classical
  have hetale : Algebra.Etale (MvPolynomial F (affineBaseRing B S hS T))
      (Algebra.LocalizedQuotient.ring g m hm) :=
    Algebra.LocalizedQuotient.etale g m hm hcard
  have hY : B.Contains (Spec (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))) :=
    contains_spec_mvPolynomial B S hS T F
  have hY' : B.Contains (Spec (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm))) :=
    contains_spec_of_finiteType B hY
  set ψ := specOverAffineBaseHom B S hS hY hY'
    (IsScalarTower.toAlgHom (affineBaseRing B S hS T) (MvPolynomial F (affineBaseRing B S hS T))
      (Algebra.LocalizedQuotient.ring g m hm))
  have hψ : Etale ((BigFppfOver.toScheme B S hS).map ψ) := by
    show Etale (X := Spec (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm)))
      (Y := Spec (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T))))
      (Spec.map (CommRingCat.ofHom
        (IsScalarTower.toAlgHom (affineBaseRing B S hS T)
          (MvPolynomial F (affineBaseRing B S hS T))
          (Algebra.LocalizedQuotient.ring g m hm)).toRingHom))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr hetale
  have hspec : ∀ {R' S' : CommRingCat.{u}} (f : R' ⟶ S'), (Spec.map f).appTop =
      (Scheme.ΓSpecIso R').hom ≫ f ≫ (Scheme.ΓSpecIso S').inv := by
    intro R' S' f
    simp [Scheme.ΓSpecIso_inv_naturality]
  -- the morphism to `Spec A[y_F]`
  set ω := levelChartBase ρ w
  set ωY : W ⟶ specOverAffineBase B S hS T (MvPolynomial F (affineBaseRing B S hS T)) hY :=
    toSpecOverAffineBase B S hS ω hY θ hθA
  have hωY : ((BigFppfOver.toScheme B S hS).map ωY).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).hom ≫
        CommRingCat.ofHom θ :=
    appTop_toSpecOverAffineBase B S hS ω hY θ hθA
  have hinv : s ≫ ωY = t ≫ ωY := by
    apply hom_ext_specOverAffineBase B S hS
    rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, hωY]
    ext x
    exact congrArg (fun k ↦ k ((Scheme.ΓSpecIso _).hom x)) hθinv
  obtain ⟨φ, hφ⟩ := exists_desc_of_isPullback B S hS hX w hR hws hwe ωY hinv
  -- the lift on the chart
  have hθ'A :
      θ'.comp (algebraMap (affineBaseRing B S hS T) (Algebra.LocalizedQuotient.ring g m hm)) =
      ((BigFppfOver.toScheme B S hS).map ω).appTop.hom := by
    rw [IsScalarTower.algebraMap_eq (affineBaseRing B S hS T)
      (MvPolynomial F (affineBaseRing B S hS T)), ← RingHom.comp_assoc, hθ', hθA]
  set β : W ⟶ specOverAffineBase B S hS T (Algebra.LocalizedQuotient.ring g m hm) hY' :=
    toSpecOverAffineBase B S hS ω hY' θ' hθ'A
  have hβapp : ((BigFppfOver.toScheme B S hS).map β).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm))).hom ≫
        CommRingCat.ofHom θ' :=
    appTop_toSpecOverAffineBase B S hS ω hY' θ' hθ'A
  have hψapp : ((BigFppfOver.toScheme B S hS).map ψ).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).hom ≫
        CommRingCat.ofHom (algebraMap (MvPolynomial F (affineBaseRing B S hS T))
          (Algebra.LocalizedQuotient.ring g m hm)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm))).inv :=
    hspec _
  have hβψ : β ≫ ψ = ωY := by
    apply hom_ext_specOverAffineBase B S hS
    rw [Functor.map_comp, Scheme.Hom.comp_appTop, hψapp, hβapp, hωY]
    ext x
    show θ' ((Scheme.ΓSpecIso (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm))).inv
      (algebraMap _ (Algebra.LocalizedQuotient.ring g m hm) ((Scheme.ΓSpecIso _).hom x)))) =
      θ ((Scheme.ΓSpecIso _).hom x)
    rw [Iso.inv_hom_id_apply, ← hθ', RingHom.comp_apply]
  have hβ : w ≫ φ = yoneda.map (β ≫ ψ) := by rw [hφ, hβψ]
  -- the thin comparison
  set a₀ := thinBase B S hS φ x₀
  set α := coefSpecialization B S hS ρ x₀ coef
  have hc₀surj : Surjective ((BigFppfOver.toScheme B S hS).map c₀) :=
    hws.property x₀ (yoneda.map ι₀) c₀ hsq₀
  have hc₀et : Etale ((BigFppfOver.toScheme B S hS).map c₀) :=
    hwe.property x₀ (yoneda.map ι₀) c₀ hsq₀
  have hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map c₀).appTop.hom :=
    (faithfullyFlat_appTop_of_flat_of_surjective _).injective
  have hca : c₀ ≫ a₀ = ι₀ ≫ ωY := by
    have ha : yoneda.map a₀ = x₀ ≫ φ := Functor.map_preimage _ _
    apply yoneda.map_injective
    rw [Functor.map_comp, ha, ← Category.assoc, ← hsq₀.w, Category.assoc, hφ, ← Functor.map_comp]
  have hca' := congrArg (fun k ↦ ((BigFppfOver.toScheme B S hS).map k).appTop) hca
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at hca'
  have hαx : ∀ x : MvPolynomial F (affineBaseRing B S hS T),
      ((BigFppfOver.toScheme B S hS).map a₀).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).inv.hom x) =
        α x := by
    intro x
    apply hinj
    have h1 : ((BigFppfOver.toScheme B S hS).map c₀).appTop.hom
        (((BigFppfOver.toScheme B S hS).map a₀).appTop.hom
          ((Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).inv.hom x)) =
        ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom
          (((BigFppfOver.toScheme B S hS).map ωY).appTop.hom
          ((Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).inv.hom x)) :=
      congrArg (fun k ↦ k.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).inv.hom x))
        hca'
    have h2 : ((BigFppfOver.toScheme B S hS).map ωY).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).inv.hom x) =
        θ x := by
      refine (congrArg (fun k ↦ k.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))).inv.hom x))
        hωY).trans (congrArg θ (Iso.inv_hom_id_apply
          (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F (affineBaseRing B S hS T)))) x))
    have h3 := congrArg (fun k ↦ k x) hθ₀
    refine h1.trans ((congrArg _ h2).trans (h3.trans ?_))
    rw [hc₀]
    rfl
  -- the pushout of rings on the thin chart
  let : Algebra (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤) := α.toAlgebra
  let : Algebra (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) :=
    ((algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤)).comp α).toAlgebra
  have : IsScalarTower (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤) Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hrel' : ∀ j, P₀.relation j = (g j).map (algebraMap (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)) := fun j ↦ (hrel j).symm
  have hbij := Algebra.LocalizedQuotient.bijective_tensorLift g m hm P₀ hrel' hmap
  have htoAlg : (Algebra.LocalizedQuotient.toAlgHom g m hm P₀ hrel' hmap :
      Algebra.LocalizedQuotient.ring g m hm →+* Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤)) =
      ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom.comp θ' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Algebra.LocalizedQuotient.jac g m hm))
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := congrArg (fun k ↦ k r) hθ'
      have h2 := congrArg (fun k ↦ k r) hθ₀
      simp only [RingHom.comp_apply] at h1 h2
      simp only [RingHom.comp_apply, RingHom.coe_coe,
        Algebra.LocalizedQuotient.toAlgHom_algebraMap, Algebra.LocalizedQuotient.quotToAlgHom_mk,
        MvPolynomial.aeval_C]
      refine h2.symm.trans ?_
      rw [← h1]
      rfl
    · intro i
      simp only [RingHom.comp_apply, RingHom.coe_coe,
        Algebra.LocalizedQuotient.toAlgHom_algebraMap, Algebra.LocalizedQuotient.quotToAlgHom_mk,
        MvPolynomial.aeval_X]
      exact (hθ'₀ i).symm
  set e₄ := (RingEquiv.ofBijective (Algebra.LocalizedQuotient.tensorLift g m hm P₀ hrel' hmap)
    hbij).toCommRingCatIso
  have h2ring : IsPushout (CommRingCat.ofHom α)
      (CommRingCat.ofHom (algebraMap (MvPolynomial F (affineBaseRing B S hS T))
        (Algebra.LocalizedQuotient.ring g m hm)))
      ((BigFppfOver.toScheme B S hS).map c₀).appTop
      (CommRingCat.ofHom (((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom.comp θ')) := by
    refine (CommRingCat.isPushout_tensorProduct (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤) (Algebra.LocalizedQuotient.ring g m hm)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e₄ rfl rfl ?_ ?_
    · ext x
      show Algebra.LocalizedQuotient.tensorLift g m hm P₀ hrel' hmap (x ⊗ₜ 1) = _
      simp only [Algebra.LocalizedQuotient.tensorLift, Algebra.TensorProduct.lift_tmul, map_one,
        mul_one, Iso.refl_hom, Category.id_comp, Algebra.ofId_apply]
      exact congrArg (fun k ↦ k x) hc₀
    · ext x
      show Algebra.LocalizedQuotient.tensorLift g m hm P₀ hrel' hmap (1 ⊗ₜ x) = _
      simp only [Algebra.LocalizedQuotient.tensorLift, Algebra.TensorProduct.lift_tmul, map_one,
        one_mul, Iso.refl_hom, Category.id_comp, CommRingCat.hom_ofHom]
      exact congrArg (fun k ↦ k x) htoAlg
  -- the same pushout, read on the global functions of the objects of the site
  have hβι : ((BigFppfOver.toScheme B S hS).map (ι₀ ≫ β)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm))).hom ≫
        CommRingCat.ofHom (((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom.comp θ') := by
    rw [Functor.map_comp, Scheme.Hom.comp_appTop, hβapp]
    rfl
  have h2 : IsPushout ((BigFppfOver.toScheme B S hS).map a₀).appTop
      ((BigFppfOver.toScheme B S hS).map ψ).appTop ((BigFppfOver.toScheme B S hS).map c₀).appTop
      ((BigFppfOver.toScheme B S hS).map (ι₀ ≫ β)).appTop := by
    refine h2ring.of_iso (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial F
      (affineBaseRing B S hS T)))).symm (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of (Algebra.LocalizedQuotient.ring g m hm))).symm
      (Iso.refl _) ?_ ?_ ?_ ?_
    · exact CommRingCat.hom_ext (RingHom.ext fun x => (hαx x).symm)
    · rw [hψapp]
      exact (Iso.inv_hom_id_assoc _ _).symm
    · rfl
    · rw [hβι, Iso.refl_hom, Category.comp_id]
      exact (Iso.inv_hom_id_assoc _ _).symm
  -- the comparison on the thin chart is an isomorphism
  have hκf : thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀ ≫ pullback.fst a₀ ψ = c₀ :=
    pullback.lift_fst _ _ _
  have hκs : thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀ ≫ pullback.snd a₀ ψ = ι₀ ≫ β :=
    pullback.lift_snd _ _ _
  have hiso : IsIso (thinComparison B S hS w φ ψ β hβ x₀ ι₀ c₀ hsq₀) :=
    isIso_of_isPushout_appTop B S hS a₀ ψ _ (by rwa [hκf, hκs])
  have hV := isAffineSpace_pullback_of_isIso_thin B S hS hX w hws hwe φ ψ β hβ x₀ ι₀ c₀ hsq₀ hx₀
    hiso
  exact exists_iso_yoneda_of_etalePresentation B S hS hX φ ψ w hws β hβ hV

end Lift

end AlgebraicGeometry.Space

end
