module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerIdealPower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GradedTowerModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedGradedPolynomialCover
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis
public import StacksFrontier.AlgebraicGeometry.GenericStalkBaseChange.SheafBasis

/-!
# The conormal algebras of a tower of adic thickenings

Let `A` be a ring, `I ⊆ A` an ideal and `X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` a tower of schemes over the adic
thickenings `Sₙ = Spec (A / I^{n+1})` with cartesian squares. For every `k` the composite
`X₀ ⟶ Xₖ` is a closed immersion with ideal `𝒥ₖ = I𝒪_{Xₖ}`, and its conormal algebra
`Cₖ = ⨁ₙ 𝒥ₖⁿ/𝒥ₖⁿ⁺¹` ([Stacks, Tag 0630]) is a sheaf of graded algebras on `X₀`. The transition
`Xₖ ⟶ Xₖ₊₁` induces the canonical homomorphism `Cₖ₊₁ ⟶ Cₖ` of [Stacks, Tag 0634].

This file supplies the geometric input of the second paragraph of the proof of
[Stacks, Tag 089A]: those canonical homomorphisms, together with the chart description of the
ideals that shows they are isomorphisms in degrees `n ≤ k`.

## Main definitions

* `Stacks.AdicTower.conormalAlg`: the conormal algebra `Cₖ` of `X₀ ⟶ Xₖ`.
* `Stacks.AdicTower.conormalStep`: the canonical homomorphism `Cₖ₊₁ ⟶ Cₖ`.
* `Stacks.AdicTower.chartOpen`: the basis of `X₀` formed by the preimages of affine opens of
  `Xₖ`.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AdicTower

variable {A : Type u} [CommRing A] {I : Ideal A} {Xn : ℕ → Scheme.{u}}
  (q : ∀ n, Xn n ⟶ adicThickening A I n) (t : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))

/-! ### Points and charts -/

include hcart in
/-- The composite transitions `X₀ ⟶ Xₖ` are surjective. -/
lemma surjective_incl (k : ℕ) : Function.Surjective (incl t k).base := by
  induction k with
  | zero => exact Function.surjective_id
  | succ k ih =>
    have : Surjective (t k) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart k).flip inferInstance
    rw [incl_succ, Scheme.Hom.comp_base]
    exact (t k).surjective.comp ih

include hcart in
/-- Taking preimages along `X₀ ⟶ Xₖ` reflects inclusions of opens. -/
lemma preimage_incl_le_iff (k : ℕ) (U V : (Xn k).Opens) :
    incl t k ⁻¹ᵁ U ≤ incl t k ⁻¹ᵁ V ↔ U ≤ V := by
  refine ⟨fun h x hx => ?_, fun h => (incl t k).preimage_mono h⟩
  obtain ⟨y, rfl⟩ := surjective_incl q t hcart k x
  exact h hx

/-- The chart `X₀ ⊇ (X₀ ⟶ Xₖ)⁻¹ U` attached to an affine open `U` of `Xₖ`. -/
abbrev chartOpen (k : ℕ) (U : (Xn k).affineOpens) : (Xn 0).Opens := incl t k ⁻¹ᵁ U.1

include hcart in
/-- **The charts form a basis of `X₀`.** `X₀ ⟶ Xₖ` is a surjective closed immersion, hence a
homeomorphism, so preimages of a basis form a basis. -/
lemma isBasis_chartOpen (k : ℕ) : Opens.IsBasis (Set.range (chartOpen t k)) := by
  have : IsClosedImmersion (incl t k) := isClosedImmersion_incl q t hcart k
  have hemb := (incl t k).isClosedEmbedding
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  -- the image of `W` is open, `incl` being a closed embedding which is surjective
  have himg : IsOpen ((incl t k).base '' (W : Set (Xn 0))) := by
    have hc := hemb.isClosedMap _ W.isOpen.isClosed_compl
    rw [Set.image_compl_eq ⟨hemb.injective, surjective_incl q t hcart k⟩] at hc
    exact isClosed_compl_iff.mp hc
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := (Xn k).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_image_of_mem _ hx) himg
  refine ⟨chartOpen t k ⟨U, hU⟩, ⟨⟨U, hU⟩, rfl⟩, hxU, fun y hy => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hUW hy
  rwa [hemb.injective hzy] at hz

/-! ### Ideal powers -/

/-- In `A / I^{m+1}`, read on the global sections of `Sₘ`, the ideal `Iʲ` lies in the `j`-th power
of the ideal `I`. -/
lemma ker_basePowHom_le_pow (m j : ℕ) (h : j ≤ m + 1) (h1 : 1 ≤ m + 1) :
    RingHom.ker (Spec.map (basePowHom A I m j h)).appTop.hom ≤
      RingHom.ker (Spec.map (basePowHom A I m 1 h1)).appTop.hom ^ j := by
  intro x hx
  set e := Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ (m + 1)))
  rw [mem_ker_appTop_iff] at hx
  simp only [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker] at hx
  have hle : (I.map (Ideal.Quotient.mk (I ^ (m + 1)))).map e.inv.hom ≤
      RingHom.ker (Spec.map (basePowHom A I m 1 h1)).appTop.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, mem_ker_appTop_iff]
    simp only [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker, pow_one]
    rwa [show e.hom.hom (e.inv.hom y) = y from e.inv_hom_id_apply y]
  have hx' : e.hom.hom x ∈ (I.map (Ideal.Quotient.mk (I ^ (m + 1)))) ^ j := by
    rwa [← Ideal.map_pow]
  have hmem := Ideal.mem_map_of_mem e.inv.hom hx'
  rw [Ideal.map_pow, show e.inv.hom (e.hom.hom x) = x from e.hom_inv_id_apply x] at hmem
  exact Ideal.pow_right_mono hle j hmem

/-- **`Iʲ𝒪_{Xₘ} ⊆ (I𝒪_{Xₘ})ʲ`** on an affine open. -/
lemma ideal_towerIdealPow_le_pow (m j : ℕ) (h : j ≤ m + 1) (h1 : 1 ≤ m + 1)
    (U : (Xn m).affineOpens) :
    (towerIdealPow q m j h).ideal U ≤ (towerIdealPow q m 1 h1).ideal U ^ j := by
  rw [ideal_towerIdealPow, ideal_towerIdealPow, ← Ideal.map_pow]
  exact Ideal.map_mono (ker_basePowHom_le_pow m j h h1)

/-- The two halves of the bijectivity of the canonical map on an affine chart, as a statement
about rings: for a surjection `φ : R → S`, an ideal `J' ⊆ S` with preimage `J`, and a kernel
inside `J^{j+1}`, the map `Jʲ/Jʲ⁺¹ → J'ʲ/J'ʲ⁺¹` is onto and one-to-one. -/
lemma pow_surj_inj_aux {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (J : Ideal R) (J' : Ideal S) (hJ : J = J'.comap φ) (j : ℕ)
    (hker : RingHom.ker φ ≤ J ^ (j + 1)) :
    (∀ b ∈ J' ^ j, ∃ a ∈ J ^ j, φ a = b) ∧
      (∀ a ∈ J ^ j, φ a ∈ J' ^ (j + 1) → a ∈ J ^ (j + 1)) ∧
      (∀ a ∈ J ^ j, φ a ∈ J' ^ j) := by
  have hmap : ∀ l : ℕ, (J ^ l).map φ = J' ^ l := fun l => by
    rw [Ideal.map_pow, hJ, Ideal.map_comap_of_surjective φ hφ]
  refine ⟨fun b hb => ?_, fun a _ ha => ?_, fun a ha => ?_⟩
  · rw [← hmap j] at hb
    exact (Ideal.mem_map_iff_of_surjective φ hφ).1 hb
  · rw [← hmap (j + 1)] at ha
    obtain ⟨c, hc, hca⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 ha
    have hsub : a - c ∈ J ^ (j + 1) := hker (by rw [RingHom.mem_ker, map_sub, hca, sub_self])
    simpa using Ideal.add_mem _ hsub hc
  · rw [← hmap j]
    exact Ideal.mem_map_of_mem φ ha

/-! ### The conormal algebras and the canonical maps between them -/

variable [hci : ∀ k, IsClosedImmersion (incl t k)] [hct : ∀ k, IsClosedImmersion (t k)]

/-- The conormal algebra `Cₖ = ⨁ₙ 𝒥ₖⁿ/𝒥ₖⁿ⁺¹` of the closed immersion `X₀ ⟶ Xₖ`. -/
abbrev conormalAlg (k : ℕ) : SheafOfModules.GradedAlgebra.{u, u} (Xn 0).ringCatSheaf :=
  (Stacks.Conormal.conormalAlgebra (incl t k)).algebra

omit hci hct in
/-- The inclusion `X₀ ⟶ Xₖ₊₁` is the inclusion `X₀ ⟶ Xₖ` followed by the transition `Xₖ ⟶ Xₖ₊₁`. -/
lemma incl_comm (k : ℕ) : 𝟙 (Xn 0) ≫ incl t (k + 1) = incl t k ≫ t k := by
  rw [Category.id_comp]
  rfl

/-- The canonical morphism of conormal algebras of [Stacks, Tag 0634] for the triangle
`X₀ ⟶ Xₖ ⟶ Xₖ₊₁`. -/
abbrev stepHom (k : ℕ) : ConormalAlgebraHom (incl t k) (incl t (k + 1)) (𝟙 (Xn 0)) :=
  (conormalAlgebraHom (incl t k) (incl t (k + 1)) (𝟙 _) (t k) (incl_comm t k)).hom

/-- The degree-`n` component of the canonical map `Cₖ₊₁ ⟶ Cₖ`, as a morphism of sheaves of
modules on `X₀`. -/
def stepApp (k : ℕ) (n : ℤ) : (conormalAlg t (k + 1)).piece n ⟶ (conormalAlg t k).piece n :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom ((stepHom t k).map n W.unop W.unop le_rfl)
      naturality := by
        intro W W' h
        ext a
        exact ((stepHom t k).map_restrict_source n W'.unop W.unop W'.unop (leOfHom h.unop)
          le_rfl (leOfHom h.unop) a).trans
          ((stepHom t k).map_restrict_target n W.unop W'.unop (leOfHom h.unop) W.unop le_rfl
            a).symm }
    (fun W r a => by
      refine ((stepHom t k).map_smul n W.unop W.unop le_rfl r a).trans ?_
      have e : (Xn 0).presheaf.map (homOfLE (le_refl W.unop)).op
          (((𝟙 (Xn 0) : Xn 0 ⟶ Xn 0).app W.unop).hom r) = r := by
        rw [show (homOfLE (le_refl W.unop)).op = 𝟙 _ from rfl, (Xn 0).presheaf.map_id]
        rfl
      exact congrArg (fun s => s • ((stepHom t k).map n W.unop W.unop le_rfl a)) e)⟩

omit hct in
/-- On sections over an open `W` of `X₀`, the map `stepApp t k n` is the degree-`n` map of
`stepHom t k` over `W`. -/
lemma stepApp_app (k : ℕ) (n : ℤ) (W : (Xn 0).Opens)
    (a : ((conormalAlg t (k + 1)).piece n).val.obj (op W)) :
    (stepApp t k n).val.app (op W) a = (stepHom t k).map n W W le_rfl a := rfl

/-- **The canonical homomorphism `Cₖ₊₁ ⟶ Cₖ`** of sheaves of graded algebras. -/
def conormalStep (k : ℕ) :
    SheafOfModules.GradedAlgebra.UnitalHom (conormalAlg t (k + 1)) (conormalAlg t k) where
  app := stepApp t k
  map_mul i j U x y := (stepHom t k).map_mul i j U.unop U.unop le_rfl x y
  map_one U := (stepHom t k).map_one U.unop U.unop le_rfl

/-! ### The canonical maps are isomorphisms in low degrees -/

omit hct in
/-- The restriction of `X₀ ⟶ Xₖ` over an open `V` of `Xₖ` is a closed immersion. -/
lemma isClosedImmersion_resLE_incl (k : ℕ) (V : (Xn k).Opens) :
    IsClosedImmersion ((incl t k).resLE V (incl t k ⁻¹ᵁ V) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

omit hci in
/-- The ideal of `X₀` in `Xₖ₊₁` on an affine chart is the preimage of the ideal of `X₀` in `Xₖ`. -/
lemma chartIdeal_succ_eq_comap (k : ℕ) (V : (Xn (k + 1)).affineOpens) :
    Stacks.Conormal.chartIdeal (incl t (k + 1)) V =
      (Stacks.Conormal.chartIdeal (incl t k) ⟨t k ⁻¹ᵁ V.1, V.2.preimage _⟩).comap
        ((t k).app V.1).hom := by
  change RingHom.ker (((incl t k).app (t k ⁻¹ᵁ V.1)).hom.comp ((t k).app V.1).hom) = _
  exact (RingHom.comap_ker _ _).symm

include hcart in
/-- The kernel of `Γ(Xₖ₊₁, V) ⟶ Γ(Xₖ, V)` is `I^{k+1}𝒪`, inside the `(k+1)`-st power of the
ideal of `X₀`. -/
lemma ker_app_transition_le (k : ℕ) (V : (Xn (k + 1)).affineOpens) :
    RingHom.ker ((t k).app V.1).hom ≤
      Stacks.Conormal.chartIdeal (incl t (k + 1)) V ^ (k + 1) := by
  have h1 : RingHom.ker ((t k).app V.1).hom =
      (towerIdealPow q (k + 1) (k + 1) (by omega)).ideal V := by
    rw [towerIdealPow_self q t hcart k, Scheme.Hom.ker_apply]
  have h2 : Stacks.Conormal.chartIdeal (incl t (k + 1)) V =
      (towerIdealPow q (k + 1) 1 (by omega)).ideal V := by
    rw [towerIdealPow_one q t hcart (k + 1), Scheme.Hom.ker_apply]
  rw [h1, h2]
  exact ideal_towerIdealPow_le_pow q (k + 1) (k + 1) _ _ V

/-- **The canonical map `Cₖ₊₁ ⟶ Cₖ` on a chart**, in terms of the local presentations: the class
of `a ∈ 𝒥ₖ₊₁ʲ` goes to the class of its image in `Γ(Xₖ, V)`. -/
lemma stepApp_localMap (k j : ℕ) (V : (Xn (k + 1)).affineOpens)
    (a : ↥(Stacks.Conormal.chartIdeal (incl t (k + 1)) V ^ j))
    (b : ↥(Stacks.Conormal.chartIdeal (incl t k) ⟨t k ⁻¹ᵁ V.1, V.2.preimage _⟩ ^ j))
    (hab : (b : Γ(Xn k, t k ⁻¹ᵁ V.1)) = ((t k).app V.1).hom a) :
    (stepApp t k j).val.app (op (chartOpen t (k + 1) V))
        ((Stacks.Conormal.conormalAlgebra (incl t (k + 1))).localMap V
          (isClosedImmersion_resLE_incl t (k + 1) V.1) j a) =
      (Stacks.Conormal.conormalAlgebra (incl t k)).localMap ⟨t k ⁻¹ᵁ V.1, V.2.preimage _⟩
        (isClosedImmersion_resLE_incl t k _) j b :=
  (conormalAlgebraHom (incl t k) (incl t (k + 1)) (𝟙 _) (t k) (incl_comm t k)).chart
    ⟨t k ⁻¹ᵁ V.1, V.2.preimage _⟩ V le_rfl _ _ le_rfl j a b
    (by rw [hab, AlgebraicGeometry.presheaf_map_homOfLE_self])

include hcart in
/-- **The canonical map `Cₖ₊₁ ⟶ Cₖ` is bijective in degree `j ≤ k` on every chart.** -/
lemma bijective_stepApp_chart (k j : ℕ) (hj : j ≤ k) (V : (Xn (k + 1)).affineOpens) :
    Function.Bijective ((stepApp t k (j : ℤ)).val.app (op (chartOpen t (k + 1) V))).hom := by
  let U : (Xn k).affineOpens := ⟨t k ⁻¹ᵁ V.1, V.2.preimage _⟩
  have hU := isClosedImmersion_resLE_incl t k U.1
  have hV := isClosedImmersion_resLE_incl t (k + 1) V.1
  have hsurjφ : Function.Surjective ((t k).app V.1).hom := Scheme.Hom.app_surjective _ _ V.2
  obtain ⟨hs, hi, hm⟩ := pow_surj_inj_aux ((t k).app V.1).hom hsurjφ _ _
    (chartIdeal_succ_eq_comap t k V) j
    ((ker_app_transition_le q t hcart k V).trans (Ideal.pow_le_pow_right (by omega)))
  have hcan : ∀ (a : ↥(Stacks.Conormal.chartIdeal (incl t (k + 1)) V ^ j))
      (b : ↥(Stacks.Conormal.chartIdeal (incl t k) U ^ j)),
      (b : Γ(Xn k, U.1)) = ((t k).app V.1).hom a →
      (stepApp t k j).val.app (op (chartOpen t (k + 1) V))
          ((Stacks.Conormal.conormalAlgebra (incl t (k + 1))).localMap V hV j a) =
        (Stacks.Conormal.conormalAlgebra (incl t k)).localMap U hU j b :=
    stepApp_localMap t k j V
  refine ⟨fun x x' hxx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := (Stacks.Conormal.conormalAlgebra (incl t (k + 1))).localMap_surjective
      V hV j x
    obtain ⟨a', rfl⟩ := (Stacks.Conormal.conormalAlgebra (incl t (k + 1))).localMap_surjective
      V hV j x'
    rw [← sub_eq_zero, ← map_sub,
      (Stacks.Conormal.conormalAlgebra (incl t (k + 1))).localMap_eq_zero_iff]
    have hmem := hm _ (a - a').2
    have h0 : (Stacks.Conormal.conormalAlgebra (incl t k)).localMap U hU j
        ⟨_, hmem⟩ = 0 := by
      rw [← hcan (a - a') ⟨_, hmem⟩ rfl, map_sub, map_sub]
      exact sub_eq_zero.mpr hxx
    rw [(Stacks.Conormal.conormalAlgebra (incl t k)).localMap_eq_zero_iff] at h0
    exact hi _ (a - a').2 h0
  · obtain ⟨b, rfl⟩ := (Stacks.Conormal.conormalAlgebra (incl t k)).localMap_surjective U hU j y
    obtain ⟨a, ha, hab⟩ := hs b b.2
    exact ⟨(Stacks.Conormal.conormalAlgebra (incl t (k + 1))).localMap V hV j ⟨a, ha⟩,
      hcan ⟨a, ha⟩ b hab.symm⟩

include hcart in
/-- **The canonical map `Cₖ₊₁ ⟶ Cₖ` is an isomorphism in every degree `n ≤ k`.** -/
lemma isIso_stepApp (k : ℕ) (n : ℤ) (hn : n ≤ k) : IsIso (stepApp t k n) := by
  refine Stacks.AlgebraicGeometry.GenericStalkBaseChange.isIso_of_isIso_val_app_basis
    (isBasis_chartOpen q t hcart (k + 1)) _ (fun V => ?_)
  rw [ConcreteCategory.isIso_iff_bijective]
  rcases lt_or_ge n 0 with hneg | hnn
  · have h0 := fun m W x => Stacks.Coherent.sections_eq_zero_of_isZero _
      ((Stacks.Conormal.conormalAlgebra (incl t m)).negative_isZero n hneg) W x
    refine ⟨fun x x' _ => (h0 _ _ x).trans (h0 _ _ x').symm, fun y => ⟨0, ?_⟩⟩
    rw [h0 k _ y, map_zero]
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
    exact bijective_stepApp_chart q t hcart k j (by exact_mod_cast hn) V

/-! ### The degree-one generators -/

section Generators

/-- The image of `x ∈ A` in the sections of a scheme over `Spec R ⟶ Spec A`, computed through
`R`. -/
lemma baseSectionHom_comp_specMap {R : CommRingCat.{u}} {Y : Scheme.{u}} (g : Y ⟶ Spec R)
    (φ : CommRingCat.of A ⟶ R) (V : Y.Opens) (x : A) :
    Stacks.Coherent.baseSectionHom A (g ≫ Spec.map φ) V x =
      Y.presheaf.map (homOfLE (le_top (a := V))).op
        (g.appTop.hom ((Scheme.ΓSpecIso R).inv.hom (φ.hom x))) := by
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x)
  simp only [CommRingCat.comp_apply] at hn
  have hx : (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) =
      (Scheme.ΓSpecIso R).inv.hom (φ.hom x) := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1
    refine hn.trans ?_
    simp
  change Y.presheaf.map _ (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map φ).appTop ≫
    g.appTop).hom x) = _
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hx]

/-- The image of `x ∈ A` is natural in the scheme. -/
lemma app_baseSectionHom {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) (g : Y ⟶ Spec (.of A))
    (V : Y.Opens) (x : A) :
    (h.app V).hom (Stacks.Coherent.baseSectionHom A g V x) =
      Stacks.Coherent.baseSectionHom A (h ≫ g) (h ⁻¹ᵁ V) x :=
  ConcreteCategory.congr_hom (h.naturality (homOfLE (le_top (a := V))).op)
    (((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom x)

/-- The structure morphism of `Xₖ` to `Spec A`. -/
abbrev towerHom (k : ℕ) : Xn k ⟶ Spec (.of A) := q k ≫ adicThickeningι A I k

include hcart in
omit hci hct in
/-- The structure morphisms to `Spec A` commute with the transition `Xₖ ⟶ Xₖ₊₁`. -/
lemma transition_towerHom (k : ℕ) : t k ≫ towerHom q (k + 1) = towerHom q k := by
  rw [towerHom, ← Category.assoc, (hcart k).w, Category.assoc, adicThickeningSucc_ι]

include hcart in
omit hci hct in
/-- The structure morphisms to `Spec A` commute with the inclusion `X₀ ⟶ Xₖ`. -/
lemma incl_towerHom (k : ℕ) : incl t k ≫ towerHom q k = towerHom q 0 := by
  induction k with
  | zero => exact Category.id_comp _
  | succ k ih => rw [incl_succ, Category.assoc, transition_towerHom q t hcart k, ih]

/-- The image of `x ∈ A` in the ring of sections of `Xₖ` over an open. -/
abbrev genElt (k : ℕ) (V : (Xn k).Opens) (x : A) : Γ(Xn k, V) :=
  Stacks.Coherent.baseSectionHom A (towerHom q k) V x

omit [∀ k, IsClosedImmersion (incl t k)] [∀ k, IsClosedImmersion (t k)] in
/-- The image of `x ∈ A` in the sections of `Xₖ` is compatible with restriction. -/
lemma genElt_restrict' (k : ℕ) {U V : (Xn k).Opens} (h : V ≤ U) (x : A) :
    (Xn k).presheaf.map (homOfLE h).op (genElt q k U x) = genElt q k V x :=
  Stacks.Coherent.baseSectionHom_restrict A (towerHom q k) h x

/-- The image of `x ∈ I` in the sections of `X₀` vanishes. -/
lemma genElt_zero_of_mem (V : (Xn 0).Opens) (x : A) (hx : x ∈ I) : genElt q 0 V x = 0 := by
  rw [genElt, towerHom, adicThickeningι, baseSectionHom_comp_specMap]
  have h0 : (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))).hom x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hx)
  rw [h0, map_zero, map_zero, map_zero]

include hcart in
omit hci hct in
/-- The image of `x ∈ I` in the sections of `Xₖ` over an affine open lies in the ideal of `X₀`. -/
lemma genElt_mem (k : ℕ) (U : (Xn k).affineOpens) (x : A) (hx : x ∈ I) :
    genElt q k U.1 x ∈ Stacks.Conormal.chartIdeal (incl t k) U := by
  rw [RingHom.mem_ker, app_baseSectionHom, incl_towerHom q t hcart k]
  exact genElt_zero_of_mem q _ x hx

include hcart in
omit hci hct in
/-- The transition `Xₖ ⟶ Xₖ₊₁` sends the image of `x ∈ A` in the sections of `Xₖ₊₁` to its image
in the sections of `Xₖ`. -/
lemma genElt_transition (k : ℕ) (V : (Xn (k + 1)).Opens) (x : A) :
    ((t k).app V).hom (genElt q (k + 1) V x) = genElt q k (t k ⁻¹ᵁ V) x := by
  rw [app_baseSectionHom, transition_towerHom q t hcart k]

end Generators

end Stacks.AdicTower

end
