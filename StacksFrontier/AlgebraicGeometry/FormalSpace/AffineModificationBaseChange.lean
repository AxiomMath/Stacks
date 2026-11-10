module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOverMap
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseFormalSpaces
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.AdicCompletion.KerEval

/-!
# Stacks 0AE5: modifications and an isomorphism on adic completions

Let `φ : A →+* R` be a homomorphism of Noetherian rings and `I ⊆ A` an ideal such that `φ`
induces an isomorphism from the `I`-adic completion of `A` to the `I R`-adic completion of `R`.
**Stacks 0AE5** says that base change along `Spec R ⟶ Spec A` is an equivalence from the
category of Stacks 0AS2 for `(A, I)` — the morphisms `X' ⟶ Spec A` of algebraic spaces which are
locally of finite type and an isomorphism over `Spec A ∖ V(I)` — to the category of Stacks 0AS2
for `(R, I R)`.

The proof is the source's. By Stacks 0ARA both categories are equivalent, through completion, to
the categories of rig-étale morphisms with locally Noetherian source over the completions
`(Spec A)_{/V(I)}` and `(Spec R)_{/V(I R)}`. Completion commutes with base change (the square of
Stacks 0GDQ), and the morphism of completions `(Spec R)_{/V(I R)} ⟶ (Spec A)_{/V(I)}` is an
isomorphism, so base change on the rig-étale side is an equivalence too. The source deduces
the isomorphism of completions from Stacks 0GBA, `X_{/T} = Spf(A^∧)`. Here it is proved
directly, on sections over affine schemes. Write `I^∧` for the image of `I` in `A^∧`. The
isomorphism `A^∧ ≅ R^∧` gives `A ⧸ I ^ n = A^∧ ⧸ (I^∧) ^ n ≅ R ⧸ (I R) ^ n` for every `n`. An
affine scheme mapping to `Spec A` with image in `V(I)` maps through some `Spec (A ⧸ I ^ n)`, so
it lifts uniquely to `Spec R`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.affineModificationBaseChange`: base change along
  `Spec R ⟶ Spec A`, from the category of Stacks 0AS2 for `(A, I)` to the one for `(R, I R)`.
* `AlgebraicGeometry.FormalSpace.affineModificationBaseChangeCompιIso`: after forgetting the
  conditions of Stacks 0AS2 it is the pullback functor along `Spec R ⟶ Spec A`.
* `AlgebraicGeometry.FormalSpace.rigEtaleOverPullback`: base change along an isomorphism of
  locally Noetherian formal algebraic spaces, on the right-hand categories of Stacks 0AR5.

## Main results

* `AlgebraicGeometry.FormalSpace.isEquivalence_affineModificationBaseChange`: **Stacks 0AE5**.
* `bijective_quotientMap_pow_of_bijective_adicCompletionMap`: an isomorphism of `I`-adic
  completions induces isomorphisms `A ⧸ I ^ n ≅ R ⧸ (I R) ^ n`.
* `AlgebraicGeometry.FormalSpace.isIso_completionSheafMap_affineOverMap`: the completion of
  `Spec R ⟶ Spec A` along `V(I)` is an isomorphism.
* `AlgebraicGeometry.FormalSpace.isEquivalence_finiteTypeBaseChangePointsFunctor_of_isIso`: base
  change between categories of Stacks 0AS2 is an equivalence when the two completion functors
  of Stacks 0AR5 are and the morphism of completions is an isomorphism.

## Implementation notes

Algebraic spaces are taken over a base scheme `S` contained in a big fppf site `B`, as
everywhere in this library, and `Spec A` lies over `S` through `s : Spec A ⟶ S`. `Spec R` lies
over `S` through `Spec R ⟶ Spec A ⟶ S`. The category of algebraic spaces over `S` with a
morphism to `Spec A` is the category of algebraic spaces over `Spec A`, so this is no
restriction. The target category of the functor is literally the category of Stacks 0AS2 for
`(R, I R)`: the inverse image of `V(I)` is identified with `V(I R)`
(`AlgebraicGeometry.FormalSpace.preimage_zeroLocusPoints`).

## References

* [Stacks Project, Tag 0AE5](https://stacks.math.columbia.edu/tag/0AE5)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
* [Stacks Project, Tag 0ARA](https://stacks.math.columbia.edu/tag/0ARA)
* [Stacks Project, Tag 0GDQ](https://stacks.math.columbia.edu/tag/0GDQ)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### The truncations of an isomorphism of adic completions -/

section Algebra

variable {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R) (I : Ideal A)

/-- The inclusion `I ^ n ≤ φ⁻¹ ((I R) ^ n)` along which `φ` descends to the truncations. -/
theorem pow_le_comap_map_pow (n : ℕ) : I ^ n ≤ ((I.map φ) ^ n).comap φ :=
  Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow])

/-- If `φ : A →+* R` induces a bijection from the `I`-adic completion of `A` to the
`I R`-adic completion of `R`, with `I` finitely generated, then `φ` induces a bijection
`A ⧸ I ^ n ≅ R ⧸ (I R) ^ n` for every `n`. -/
theorem bijective_quotientMap_pow_of_bijective_adicCompletionMap (hI : I.FG)
    (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((I.map φ) ^ n) φ (pow_le_comap_map_pow φ I n)) := by
  set ψ := adicCompletionMap φ I (I.map φ) le_rfl
  have hev (x : AdicCompletion I A) :
      AdicCompletion.evalₐ (I.map φ) n (ψ x) =
        Ideal.quotientMap ((I.map φ) ^ n) φ (pow_le_comap_map_pow φ I n)
          (AdicCompletion.evalₐ I n x) :=
    adicCompletionMap_evalₐ φ I (I.map φ) le_rfl n x
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := AdicCompletion.surjective_evalₐ I n a
    have hx : ψ x ∈ RingHom.ker (AdicCompletion.evalₐ (I.map φ) n).toRingHom :=
      RingHom.mem_ker.mpr ((hev x).trans ha)
    rw [AdicCompletion.ker_evalₐ_eq_map_pow (I.map φ) (hI.map φ) n, ← Ideal.map_pow,
      Ideal.map_map, ← adicCompletionMap_comp_algebraMap φ I (I.map φ) le_rfl,
      ← Ideal.map_map] at hx
    have hx' : x ∈ ((I ^ n).map (algebraMap A (AdicCompletion I A))) := by
      rwa [← Ideal.comap_map_of_bijective ψ h (I := (I ^ n).map _)]
    rwa [← AdicCompletion.ker_evalₐ_eq_map_pow I hI n, RingHom.mem_ker] at hx'
  · obtain ⟨z, rfl⟩ := AdicCompletion.surjective_evalₐ (I.map φ) n y
    obtain ⟨x, rfl⟩ := h.2 z
    exact ⟨_, (hev x).symm⟩

/-- Two ring maps out of `R` which agree after composing with `φ` and kill `(I R) ^ n` agree,
when `A → R ⧸ (I R) ^ n` is surjective. -/
theorem ringHom_ext_of_surjective_quotientMap {C : Type*} [CommRing C] {n : ℕ}
    (hsurj : Function.Surjective
      (Ideal.quotientMap ((I.map φ) ^ n) φ (pow_le_comap_map_pow φ I n)))
    {σ₁ σ₂ : R →+* C} (h : σ₁.comp φ = σ₂.comp φ)
    (h₁ : (I.map φ) ^ n ≤ RingHom.ker σ₁) (h₂ : (I.map φ) ^ n ≤ RingHom.ker σ₂) :
    σ₁ = σ₂ := by
  ext r
  obtain ⟨q, hq⟩ := hsurj (Ideal.Quotient.mk _ r)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hq
  have e₁ : σ₁ (φ a - r) = 0 := h₁ hq
  have e₂ : σ₂ (φ a - r) = 0 := h₂ hq
  rw [map_sub, sub_eq_zero] at e₁ e₂
  rw [← e₁, ← e₂]
  exact congrArg (fun σ : A →+* C ↦ σ a) h

end Algebra

/-! ### Lifting morphisms from affine schemes supported on `V(I)` -/

namespace AlgebraicGeometry

variable {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R) (I : Ideal A)

/-- A morphism from an affine scheme `X` to `Spec T` is induced by a ring map `T →+* Γ(X, ⊤)`. -/
private theorem exists_spec_map_eq_isoSpec_inv_comp {T : Type u} [CommRing T] {X : Scheme.{u}}
    [IsAffine X] (w : X ⟶ Spec (.of T)) :
    ∃ τ : T →+* Γ(X, ⊤), Spec.map (CommRingCat.ofHom τ) = X.isoSpec.inv ≫ w :=
  ⟨(Spec.preimage (X.isoSpec.inv ≫ w)).hom, Spec.map_preimage _⟩

/-- Let `φ : A →+* R` induce bijections `A ⧸ I ^ n ≅ R ⧸ (I R) ^ n` for all `n`, with `I`
finitely generated. A morphism from an affine scheme `X` to `Spec A` whose image lies in `V(I)`
lifts uniquely along `Spec R ⟶ Spec A`. -/
theorem existsUnique_lift_spec_of_bijective_quotientMap (hI : I.FG)
    (hbij : ∀ n, Function.Bijective
      (Ideal.quotientMap ((I.map φ) ^ n) φ (pow_le_comap_map_pow φ I n)))
    {X : Scheme.{u}} [IsAffine X] (y : X ⟶ Spec (.of A))
    (hy : ∀ x, y x ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃! z : X ⟶ Spec (.of R), z ≫ Spec.map (CommRingCat.ofHom φ) = y := by
  obtain ⟨ρ, hρ⟩ := exists_spec_map_eq_isoSpec_inv_comp y
  have hrad : I ≤ (RingHom.ker ρ).radical := by
    intro a ha
    have hnil : IsNilpotent (ρ a) := nilpotent_iff_mem_prime.mpr fun P hP => by
      have ht' : (Spec.map (CommRingCat.ofHom ρ)) (⟨P, hP⟩ : PrimeSpectrum Γ(X, ⊤)) ∈
          PrimeSpectrum.zeroLocus (I : Set A) := by
        rw [hρ]
        exact hy (X.isoSpec.inv (⟨P, hP⟩ : PrimeSpectrum Γ(X, ⊤)))
      exact ht' ha
    obtain ⟨n, hn⟩ := hnil
    exact ⟨n, RingHom.mem_ker.mpr ((map_pow ρ a n).trans hn)⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hI
  let e := RingEquiv.ofBijective _ (hbij n)
  let ρ' : R →+* Γ(X, ⊤) :=
    (Ideal.Quotient.lift (I ^ n) ρ fun a ha ↦ RingHom.mem_ker.mp (hn ha)).comp
      (e.symm.toRingHom.comp (Ideal.Quotient.mk _))
  have hρ' : ρ'.comp φ = ρ := by
    ext a
    change Ideal.Quotient.lift (I ^ n) ρ (fun a ha ↦ RingHom.mem_ker.mp (hn ha))
      (e.symm (Ideal.Quotient.mk _ (φ a))) = ρ a
    have : e.symm (Ideal.Quotient.mk _ (φ a)) = Ideal.Quotient.mk _ a := e.symm_apply_eq.mpr rfl
    rw [this, Ideal.Quotient.lift_mk]
  have hker : ∀ σ : R →+* Γ(X, ⊤), σ.comp φ = ρ → (I.map φ) ^ n ≤ RingHom.ker σ := by
    intro σ hσ
    rwa [← Ideal.map_pow, Ideal.map_le_iff_le_comap, RingHom.comap_ker, hσ]
  have hspec : ∀ σ : R →+* Γ(X, ⊤),
      Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (σ.comp φ)) := by
    intro σ
    rw [← Spec.map_comp]
    rfl
  refine ⟨X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ'), ?_, fun z hz ↦ ?_⟩
  · dsimp only
    rw [Category.assoc, hspec, hρ', hρ, Iso.hom_inv_id_assoc]
  · obtain ⟨σ, hσ⟩ := exists_spec_map_eq_isoSpec_inv_comp z
    have hσφ : σ.comp φ = ρ := by
      have h1 : Spec.map (CommRingCat.ofHom (σ.comp φ)) = Spec.map (CommRingCat.ofHom ρ) := by
        rw [← hspec, hσ, Category.assoc, hz, hρ]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have hσρ : σ = ρ' :=
      ringHom_ext_of_surjective_quotientMap φ I (hbij n).2 (hσφ.trans hρ'.symm)
        (hker σ hσφ) (hker ρ' hρ')
    rw [← hσρ, hσ, Iso.hom_inv_id_assoc]

end AlgebraicGeometry

/-! ### The completions of `Spec A` and `Spec R` along `V(I)` and `V(I R)` -/

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- A morphism of presheaves of `Type (u + 1)` on the big fppf site of `S` which is bijective on
the sections over every affine object becomes an isomorphism after sheafification: the affine
objects form a dense subsite, so the morphism is locally injective and locally surjective. -/
theorem W_of_bijective_app_of_isAffine {F₁ F₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (f : F₁ ⟶ F₂)
    (hf : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      Function.Bijective (f.app (op V))) :
    (BigFppfOver.topology B S hS).W f := by
  have : (BigAffineFppf.inclusion B S hS).IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  have hinj : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) f := ⟨fun {U} x y hxy ↦ by
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Functor.IsCoverDense.is_cover (G := BigAffineFppf.inclusion B S hS)
        (K := BigFppfOver.topology B S hS) U.unop)
    rintro Y g ⟨st⟩
    have key : F₁.map st.map.op x = F₁.map st.map.op y := by
      apply (hf ((BigAffineFppf.inclusion B S hS).obj st.obj) st.obj.property).1
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
    change F₁.map g.op x = F₁.map g.op y
    rw [← st.fac, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key]⟩
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f := ⟨fun {U} t ↦ by
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Functor.IsCoverDense.is_cover (G := BigAffineFppf.inclusion B S hS)
        (K := BigFppfOver.topology B S hS) U)
    rintro Y g ⟨st⟩
    obtain ⟨t', ht'⟩ :=
      (hf ((BigAffineFppf.inclusion B S hS).obj st.obj) st.obj.property).2 (F₂.map st.map.op t)
    refine ⟨F₁.map st.lift.op t', ?_⟩
    rw [NatTrans.naturality_apply, ht', ← Functor.map_comp_apply, ← op_comp, st.fac]⟩
  exact (BigFppfOver.topology B S hS).W_of_isLocallyBijective f

variable {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R) (I : Ideal A)
  (hA : B.Contains (Spec (.of A))) (hR : B.Contains (Spec (.of R))) (s : Spec (.of A) ⟶ S)

/-- The zero locus `V(I)` is a closed set of points of the presheaf represented by `Spec A`. -/
theorem isClosed_zeroLocusPoints : IsClosed (zeroLocusPoints B S hS hA s I) := by
  have h := Set.image_preimage_eq (PrimeSpectrum.zeroLocus (I : Set A))
    (Space.surjective_pointsToScheme B S hS (affineOver B S hS hA s))
  refine (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B S hS _ _).2 ?_
  rw [zeroLocusPoints_eq_preimage_pointsToScheme]
  exact (congrArg IsClosed h).mpr (PrimeSpectrum.isClosed_zeroLocus _)

/-- Over an affine object of the site, the map from the sections of the completion of
`Spec R` along `V(I R)` to those of the completion of `Spec A` along `V(I)` is bijective, when
`A ⧸ I ^ n ≅ R ⧸ (I R) ^ n` for every `n`: a section is a morphism from an affine scheme to
`Spec A` supported on `V(I)`, and it lifts uniquely to `Spec R`. -/
theorem bijective_completionMap_app_of_isAffine (hI : I.FG)
    (hbij : ∀ n, Function.Bijective
      (Ideal.quotientMap ((I.map φ) ^ n) φ (pow_le_comap_map_pow φ I n)))
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    Function.Bijective ((Space.completionMap B S hS (yoneda.map (affineOverMap φ hA hR s))
      (zeroLocusPoints B S hS hA s I)).app (op V)) := by
  let G := affineOverMap (hS := hS) φ hA hR s
  have hG : (BigFppfOver.toScheme B S hS).map G = Spec.map (CommRingCat.ofHom φ) := rfl
  refine ⟨fun x₁ x₂ h ↦ ?_, fun ⟨⟨y⟩, hy⟩ ↦ ?_⟩
  · have h' : x₂.1.down ≫ G = x₁.1.down ≫ G := (congrArg (fun t ↦ t.1.down) h).symm
    have hy : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA s))
        (zeroLocusPoints B S hS hA s I) V (x₁.1.down ≫ G) :=
      ((Space.completionMap B S hS (yoneda.map G) (zeroLocusPoints B S hS hA s I)).app
        (op V) x₁).2
    have hy' := (hasImageIn_zeroLocusPoints_iff B S hS hA s I V _).mp hy
    obtain ⟨z, -, huniq⟩ := existsUnique_lift_spec_of_bijective_quotientMap φ I hI hbij
      ((BigFppfOver.toScheme B S hS).map (x₁.1.down ≫ G)) hy'
    have e (x : type_of% x₁) (hx : x.1.down ≫ G = x₁.1.down ≫ G) :=
      huniq ((BigFppfOver.toScheme B S hS).map x.1.down)
        (((BigFppfOver.toScheme B S hS).map_comp x.1.down G).symm.trans
          (congrArg (BigFppfOver.toScheme B S hS).map hx))
    exact Subtype.ext (ULift.ext
      ((BigFppfOver.toScheme B S hS).map_injective
        ((e x₁ rfl).trans (e x₂ h').symm)))
  · have hy' := (hasImageIn_zeroLocusPoints_iff B S hS hA s I V y).mp hy
    obtain ⟨z, hz, -⟩ := existsUnique_lift_spec_of_bijective_quotientMap φ I hI hbij
      ((BigFppfOver.toScheme B S hS).map y) hy'
    let x : V ⟶ affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s) :=
      Over.homMk (ObjectProperty.homMk z) (by
        apply ObjectProperty.hom_ext
        change z ≫ (Spec.map (CommRingCat.ofHom φ) ≫ s) = B.inclusion.map V.hom
        rw [← Category.assoc, hz]
        exact congrArg (fun t ↦ B.inclusion.map t) (Over.w y))
    have hx : Space.HasImageIn B S hS
        (yoneda.obj (affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s)))
        (Space.pointsMap B S hS _ (yoneda.map G) ⁻¹' zeroLocusPoints B S hS hA s I) V x := by
      rw [preimage_zeroLocusPoints]
      refine (hasImageIn_zeroLocusPoints_iff B S hS hR _ (I.map φ) V x).mpr fun p ↦ ?_
      have hp := hy' p
      rw [← hz] at hp
      change PrimeSpectrum.comap φ (z p) ∈ _ at hp
      change ((I.map φ : Ideal R) : Set R) ⊆ (z p).asIdeal
      simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at hp
      rw [SetLike.coe_subset_coe]
      exact Ideal.map_le_iff_le_comap.mpr hp
    refine ⟨⟨⟨x⟩, hx⟩, Subtype.ext (ULift.ext ?_)⟩
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hz

/-- **The completion of `Spec R ⟶ Spec A` along `V(I)` is an isomorphism** when `φ : A →+* R`
induces a bijection on the `I`-adic and `I R`-adic completions, `I` being finitely generated. -/
theorem isIso_completionSheafMap_affineOverMap (hI : I.FG)
    (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl)) :
    IsIso (Space.completionSheafMap B S hS (yoneda.map (affineOverMap φ hA hR s))
      (zeroLocusPoints B S hS hA s I)) := by
  have hW := W_of_bijective_app_of_isAffine (hS := hS) _ fun V hV ↦
    bijective_completionMap_app_of_isAffine φ I hA hR s hI
      (bijective_quotientMap_pow_of_bijective_adicCompletionMap φ I hI h) V hV
  rwa [(BigFppfOver.topology B S hS).W_iff_isIso_map_of_adjunction
    (plusPlusAdjunction (BigFppfOver.topology B S hS) (Type (u + 1)))] at hW

/-! ### Base change along an isomorphism of formal algebraic spaces -/

section PullbackAlongIso

variable (B S hS) in
/-- The objects of the right-hand category of Stacks 0AR5 over a formal algebraic space `Y`:
morphisms `W ⟶ Y` of formal algebraic spaces with `W` locally Noetherian, which are
rig-étale. -/
abbrev IsRigEtaleOverWithNoetherianSource (Y : FppfSheaf B S hS) : ObjectProperty (Over Y) :=
  fun W => IsFormalAlgebraicSpace B S hS W.left ∧ IsLocallyNoetherian B S hS W.left ∧
    IsRigEtale B S hS W.hom

variable {Y₁ Y : FppfSheaf B S hS} (e : Y₁ ⟶ Y) [IsIso e]
  (hY₁ : IsLocallyNoetherian B S hS Y₁) (hY : IsLocallyNoetherian B S hS Y)

include hY₁ hY in
/-- The base change of a rig-étale morphism with locally Noetherian source along an
isomorphism of locally Noetherian formal algebraic spaces is again one. -/
theorem isRigEtaleOverWithNoetherianSource_pullback (W : Over Y)
    (hW : IsRigEtaleOverWithNoetherianSource B S hS Y W) :
    IsRigEtaleOverWithNoetherianSource B S hS Y₁ ((Over.pullback e).obj W) := by
  have : HasPullback W.hom e := hasPullback_of_right_iso W.hom e
  let i : Limits.pullback W.hom e ≅ W.left := asIso (pullback.fst W.hom e)
  exact ⟨isFormalAlgebraicSpace_of_iso B S hS i hW.1,
    isLocallyNoetherian_of_iso B S hS i.symm hW.2.1,
    isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS W.hom e hW.2.1 hY hY₁ hW.2.2
      (isAdicMorphism_of_isIso B S hS e)⟩

/-- Base change along an isomorphism `e : Y₁ ⟶ Y` of locally Noetherian formal algebraic spaces,
on the right-hand categories of Stacks 0AR5. -/
def rigEtaleOverPullback :
    (IsRigEtaleOverWithNoetherianSource B S hS Y).FullSubcategory ⥤
      (IsRigEtaleOverWithNoetherianSource B S hS Y₁).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Over.pullback e) fun W =>
    isRigEtaleOverWithNoetherianSource_pullback e hY₁ hY W.obj W.property

/-- Base change along an isomorphism is an equivalence of slice categories. -/
instance isEquivalence_over_pullback_of_isIso : (Over.pullback e).IsEquivalence :=
  Functor.isEquivalence_of_iso
    ((Over.mapIso (asIso e)).toAdjunction.rightAdjointUniq (Over.mapPullbackAdj e))

/-- Base change along an isomorphism is an equivalence of the right-hand categories of
Stacks 0AR5. -/
theorem isEquivalence_rigEtaleOverPullback : (rigEtaleOverPullback e hY₁ hY).IsEquivalence := by
  have hff : (rigEtaleOverPullback e hY₁ hY).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
      (((ObjectProperty.fullyFaithfulι (IsRigEtaleOverWithNoetherianSource B S hS Y)).comp
        (Functor.FullyFaithful.ofFullyFaithful (Over.pullback e))).ofIso
          (ObjectProperty.liftCompιIso _ _ _).symm)
  have := hff.full
  have := hff.faithful
  have : (rigEtaleOverPullback e hY₁ hY).EssSurj := ⟨fun W₁ => ⟨⟨(Over.pullback (inv e)).obj W₁.obj,
    isRigEtaleOverWithNoetherianSource_pullback (inv e) hY hY₁ W₁.obj W₁.property⟩,
    ⟨(ObjectProperty.fullyFaithfulι _).preimageIso
      ((Over.pullbackComp e (inv e)).symm.app W₁.obj ≪≫
        eqToIso (congrArg (fun k => (Over.pullback k).obj W₁.obj) (IsIso.hom_inv_id e)) ≪≫
        Over.pullbackId.app W₁.obj)⟩⟩⟩
  exact { }

end PullbackAlongIso

/-! ### Base change of finite-type modifications along a map inducing an isomorphism of
completions -/

/-- Let `g : X₁ ⟶ X` be a morphism of locally Noetherian algebraic spaces over `S` and
`T ⊆ |X|` closed. If the completion functors of Stacks 0AR5 for `(X, T)` and `(X₁, |g|⁻¹T)` are
equivalences (Stacks 0ARB) and `X_{1, /|g|⁻¹T} ⟶ X_{/T}` is an isomorphism, then base change
along `g` is an equivalence between the categories of Stacks 0AS2. -/
theorem isEquivalence_finiteTypeBaseChangePointsFunctor_of_isIso
    {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₁sp : IsAlgebraicSpace B S hS X₁)
    (hXsp : IsAlgebraicSpace B S hS X) (hX₁ : Space.IsLocallyNoetherian B S hS X₁)
    (hX : Space.IsLocallyNoetherian B S hS X) (g : X₁ ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T)
    [(completionModificationFunctor T hT hXsp hX).IsEquivalence]
    [(completionModificationFunctor (Space.pointsMap B S hS X₁ g ⁻¹' T)
      (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁sp hX₁).IsEquivalence]
    [IsIso (Space.completionSheafMap B S hS g T)] :
    (Space.finiteTypeBaseChangePointsFunctor hX₁sp hXsp g T).IsEquivalence := by
  let D := rigEtaleOverPullback (Space.completionSheafMap B S hS g T)
    (isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX₁sp hX₁ _
      (hT.preimage (Space.continuous_pointsMap B S hS g)))
    (isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hXsp hX T hT)
  have : D.IsEquivalence := isEquivalence_rigEtaleOverPullback _ _ _
  let F₁ := completionModificationFunctor (Space.pointsMap B S hS X₁ g ⁻¹' T)
    (hT.preimage (Space.continuous_pointsMap B S hS g)) hX₁sp hX₁
  let sq := Space.restrictedCompletionBaseChangeSquareIso B S hS g T
    (A := Space.finiteTypeBaseChangePointsFunctor hX₁sp hXsp g T)
    (F := completionModificationFunctor T hT hXsp hX) (F₁ := F₁) (D := D)
    (Space.finiteTypeBaseChangePointsFunctorCompιIso hX₁sp hXsp g T)
    (eqToIso (completionModificationFunctor_comp_ι T hT hXsp hX))
    (eqToIso (completionModificationFunctor_comp_ι _ _ hX₁sp hX₁))
    (ObjectProperty.liftCompιIso _ _ _)
  have : (Space.finiteTypeBaseChangePointsFunctor hX₁sp hXsp g T ⋙ F₁).IsEquivalence :=
    Functor.isEquivalence_of_iso sq.symm
  exact Functor.isEquivalence_of_comp_right _ F₁

/-- Base change along `g : X₁ ⟶ X`, read through a presentation `T₁` of the inverse image of
`T`, is an equivalence as soon as `finiteTypeBaseChangePointsFunctor` is. -/
theorem isEquivalence_finiteTypeBaseChangeFunctorOfEq_of_preimage_eq
    {X₁ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₁sp : IsAlgebraicSpace B S hS X₁)
    (hXsp : IsAlgebraicSpace B S hS X) (g : X₁ ⟶ X) (T : Set (Space.points B S hS X))
    (T₁ : Set (Space.points B S hS X₁)) (hT₁ : Space.pointsMap B S hS X₁ g ⁻¹' T = T₁)
    (h : (Space.openSubspaceOfPoints B S hS X Tᶜ).preimage g =
      Space.openSubspaceOfPoints B S hS X₁ T₁ᶜ)
    [hE : (Space.finiteTypeBaseChangePointsFunctor hX₁sp hXsp g T).IsEquivalence] :
    (Space.finiteTypeBaseChangeFunctorOfEq hX₁sp hXsp g _ _ h).IsEquivalence := by
  subst hT₁
  exact hE

/-! ### Stacks 0AE5 -/

variable (B S hS)

/-- Base change along `Spec R ⟶ Spec A`, from the category of Stacks 0AS2 for `(A, I)` — the
morphisms `X' ⟶ Spec A` of algebraic spaces over `S` which are locally of finite type and an
isomorphism over `Spec A ∖ V(I)` — to the category of Stacks 0AS2 for `(R, I R)`. -/
def affineModificationBaseChange :
    Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (affineOver B S hS hA s)) (zeroLocusPoints B S hS hA s I)ᶜ) ⥤
    Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS
      (yoneda.obj (affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s)))
      (zeroLocusPoints B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s) (I.map φ))ᶜ) :=
  Space.finiteTypeBaseChangeFunctorOfEq (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) (yoneda.map (affineOverMap φ hA hR s)) _ _
    (by rw [Space.preimage_openSubspaceOfPoints_compl, preimage_zeroLocusPoints])

/-- `affineModificationBaseChange` is base change: after forgetting the conditions of
Stacks 0AS2 it is the pullback functor along `Spec R ⟶ Spec A`. -/
def affineModificationBaseChangeCompιIso :
    affineModificationBaseChange B S hS φ I hA hR s ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Over.pullback (yoneda.map (affineOverMap φ hA hR s)) :=
  Space.finiteTypeBaseChangeFunctorOfEqCompιIso _ _ _ _ _ _

/-- **Stacks 0AE5.** Let `φ : A →+* R` be a homomorphism of Noetherian rings inducing an
isomorphism from the `I`-adic completion of `A` to the `I R`-adic completion of `R`, for an
ideal `I ⊆ A`. Then base change along `Spec R ⟶ Spec A` is an equivalence from the category of
Stacks 0AS2 for `(A, I)` to the category of Stacks 0AS2 for `(R, I R)`. -/
@[stacks 0AE5]
theorem isEquivalence_affineModificationBaseChange [IsNoetherianRing A] [IsNoetherianRing R]
    (h : Function.Bijective (adicCompletionMap φ I (I.map φ) le_rfl)) :
    (affineModificationBaseChange B S hS φ I hA hR s).IsEquivalence := by
  have hT := isClosed_zeroLocusPoints (hS := hS) I hA s
  let G := yoneda.map (affineOverMap (hS := hS) φ hA hR s)
  have := isEquivalence_completionModificationFunctor_affineOver hA s _ hT
  have := isEquivalence_completionModificationFunctor_affineOver hR
    (Spec.map (CommRingCat.ofHom φ) ≫ s) _ (hT.preimage (Space.continuous_pointsMap B S hS G))
  have := isIso_completionSheafMap_affineOverMap (hS := hS) φ I hA hR s I.fg_of_isNoetherianRing h
  have := isEquivalence_finiteTypeBaseChangePointsFunctor_of_isIso
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (Space.isLocallyNoetherian_yoneda_affineOver hR _)
    (Space.isLocallyNoetherian_yoneda_affineOver hA s) G _ hT
  exact isEquivalence_finiteTypeBaseChangeFunctorOfEq_of_preimage_eq _ _ G _ _
    (preimage_zeroLocusPoints φ hA hR s I) _

end AlgebraicGeometry.FormalSpace
