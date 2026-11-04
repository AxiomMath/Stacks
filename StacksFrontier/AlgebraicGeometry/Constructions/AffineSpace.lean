module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.FPAlgebraSheaf.Polynomial
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecTransport

/-!
# Affine `n`-space over a scheme

Affine `n`-space over a scheme `S` is the relative spectrum `𝐀ⁿ_S = Spec_S(𝒪_S[T_1, …, T_n])`
of the polynomial algebra over the structure sheaf. This file constructs it, identifies the
polynomial algebra sheaf with the sheaf associated to the presheaf `U ↦ 𝒪_S(U)[T_1, …, T_n]`,
and identifies `𝐀ⁿ_S` with Mathlib's `𝔸(n; S) = S ×_{Spec ℤ} Spec ℤ[T_1, …, T_n]`.

## Main definitions

* `Stacks.AffineSpace.polynomialPresheaf S σ` is the presheaf `U ↦ 𝒪_S(U)[T_i, i ∈ σ]`, the
  presheaf `Stacks.Sites.FreeAlgebra.polynomialPresheaf` of polynomial rings on the constant
  presheaf of variables, and `Stacks.AffineSpace.polynomialSheafification S σ` its
  sheafification `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf`, as a sheaf of `𝒪_S`-algebras.
* `Stacks.AffineSpace.comparison` evaluates `T_i` at the `i`-th coordinate function of
  `𝔸(σ; S)`: a map from that presheaf to the polynomial algebra sheaf
  `Stacks.FPAlgebraSheaf.polynomialAlgebra S σ = π_* 𝒪_{𝔸(σ; S)}`.
* `Stacks.AffineSpace.sheafificationIso`: the polynomial algebra sheaf is, as a sheaf of
  `𝒪_S`-algebras, the sheafification of `U ↦ 𝒪_S(U)[T_i]`.
* `Stacks.AffineSpace.affineSpace S σ` is the relative spectrum of that sheaf, which is
  quasi-coherent by `Stacks.AffineSpace.isQuasicoherent_polynomialSheafification`, as a scheme
  over `S`, and `Stacks.AffineSpace.affineNSpace S n` is affine `n`-space.
* `Stacks.AffineSpace.affineSpaceIso` identifies it with `𝔸(σ; S)` over `S`, and
  `Stacks.AffineSpace.affineSpaceSpecIso` with `Spec R[T_i]` over an affine base `Spec R`.

## Main results

* `Stacks.AffineSpace.comparisonApp_bijective`: over an affine open `U` the comparison
  `𝒪_S(U)[T_i] ⟶ Γ(𝔸(σ; S), π⁻¹(U))` is bijective.
* `Stacks.AffineSpace.bijective_toSheafify_app`: over an affine open `U` the sections of the
  sheafification of `U ↦ 𝒪_S(U)[T_i]` are `𝒪_S(U)[T_i]`.

## Implementation notes

Over an affine open `U`, the preimage `π⁻¹(U)` is identified with `𝔸(σ; U)` through the
cartesian square `AlgebraicGeometry.AffineSpace.isPullback_map` along `U.ι`, and
`AlgebraicGeometry.AffineSpace.isoOfIsAffine` computes the global sections of `𝔸(σ; U)`. The
comparison is therefore bijective over a basis of the topology, hence locally injective and
locally surjective, so the morphism it induces out of the sheafification is an isomorphism.

## References

* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace Stacks.AffineSpace

variable (S : Scheme.{u}) (σ : Type u)

/-- The constant presheaf of sets `U ↦ σ` on a scheme `S`, the variables `T_i`. -/
abbrev polynomialVariables : S.Opensᵒᵖ ⥤ Type u := (Functor.const S.Opensᵒᵖ).obj σ

/-- The presheaf of commutative rings `U ↦ 𝒪_S(U)[T_i, i ∈ σ]` on a scheme `S`. -/
abbrev polynomialPresheaf : S.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  Sites.FreeAlgebra.polynomialPresheaf (Opens.grothendieckTopology S) S.sheaf
    (polynomialVariables S σ)

/-- The sheaf of commutative `𝒪_S`-algebras associated to the presheaf `U ↦ 𝒪_S(U)[T_i]`, with
the inclusion of constants as structure morphism. -/
abbrev polynomialSheafification : AlgebraSheaf S :=
  Under.mk (Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology S)
    S.sheaf (polynomialVariables S σ))

/-! ### Comparison with the pushforward of the structure sheaf of `𝔸(σ; S)` -/

/-- On sections over `U`, the comparison `𝒪_S(U)[T_i] ⟶ Γ(𝔸(σ; S), π⁻¹(U))` sends a constant to
its pullback along `π` and `T_i` to the restriction of the `i`-th coordinate function. -/
def comparisonApp (U : S.Opens) :
    MvPolynomial σ Γ(S, U) →+* Γ(𝔸(σ; S), (𝔸(σ; S) ↘ S) ⁻¹ᵁ U) :=
  eval₂Hom ((𝔸(σ; S) ↘ S).app U).hom fun i =>
    (𝔸(σ; S).presheaf.map (homOfLE le_top).op).hom (AffineSpace.coord S i)

/-- The coordinate functions of `𝔸(σ; S)`, restricted to the preimages `π⁻¹(U)`, as a morphism
from the variables to the underlying presheaf of sets of `π_* 𝒪_{𝔸(σ; S)}`. -/
def coordinates : polynomialVariables S σ ⟶
    Sites.FreeAlgebra.underlyingPresheaf _ (FPAlgebraSheaf.polynomialAlgebra S σ).right where
  app U := TypeCat.ofHom fun i =>
    (𝔸(σ; S).presheaf.map (homOfLE le_top).op).hom (AffineSpace.coord S i)
  naturality U V f := by
    ext i
    change (𝔸(σ; S).presheaf.map (homOfLE le_top).op).hom (AffineSpace.coord S i) =
      (𝔸(σ; S).presheaf.map _).hom
        ((𝔸(σ; S).presheaf.map (homOfLE le_top).op).hom (AffineSpace.coord S i))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

/-- The comparison map from the presheaf `U ↦ 𝒪_S(U)[T_i]` to `π_* 𝒪_{𝔸(σ; S)}`, sending a
constant to its pullback along `π` and `T_i` to the `i`-th coordinate function. -/
abbrev comparison : polynomialPresheaf S σ ⟶ (FPAlgebraSheaf.polynomialAlgebra S σ).right.obj :=
  Sites.FreeAlgebra.polynomialEvaluation _ S.sheaf _ (polynomialVariables S σ)
    (FPAlgebraSheaf.polynomialAlgebra S σ).hom (coordinates S σ)

/-- On sections over `U`, the comparison map is `comparisonApp`. -/
theorem comparison_app (U : S.Opens) :
    (comparison S σ).app (op U) = CommRingCat.ofHom (comparisonApp S σ U) :=
  rfl

/-- Over an affine scheme `T`, the map `Γ(T, ⊤)[T_i] ⟶ Γ(𝔸(σ; T), ⊤)` sending `T_i` to the
`i`-th coordinate is bijective. -/
theorem bijective_eval₂Hom_coord (T : Scheme.{u}) [IsAffine T] :
    Function.Bijective (eval₂Hom ((𝔸(σ; T) ↘ T).appTop).hom (AffineSpace.coord T)) := by
  have h := (AffineSpace.isoOfIsAffine σ T).isIso_hom
  rw [AffineSpace.isoOfIsAffine_hom] at h
  exact isIso_SpecMap_iff.mp (IsIso.of_isIso_comp_left 𝔸(σ; T).toSpecΓ (Spec.map
    (CommRingCat.ofHom (eval₂Hom ((𝔸(σ; T) ↘ T).appTop).hom (AffineSpace.coord T)))))

/-- **Over an affine open `U` of `S`, the comparison `𝒪_S(U)[T_i] ⟶ Γ(𝔸(σ; S), π⁻¹(U))` is
bijective.** -/
theorem comparisonApp_bijective {U : S.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (comparisonApp S σ U) := by
  have : IsAffine U.toScheme := hU
  have sq := AffineSpace.isPullback_map (n := σ) U.ι
  have : IsOpenImmersion (AffineSpace.map σ U.ι) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip (inferInstanceAs
      (IsOpenImmersion U.ι))
  let E : 𝔸(σ; U.toScheme) ≅ ((𝔸(σ; S) ↘ S) ⁻¹ᵁ U).toScheme :=
    sq.isoPullback ≪≫ pullbackRestrictIsoRestrict (𝔸(σ; S) ↘ S) U
  have hE : E.hom ≫ ((𝔸(σ; S) ↘ S) ⁻¹ᵁ U).ι = AffineSpace.map σ U.ι := by
    simp only [E, Iso.trans_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_ι]
    exact sq.isoPullback_hom_fst
  have hrange : (𝔸(σ; S) ↘ S) ⁻¹ᵁ U ≤ (AffineSpace.map σ U.ι).opensRange := by
    have (f : 𝔸(σ; U.toScheme) ⟶ 𝔸(σ; S)) [IsOpenImmersion f]
        (hf : E.hom ≫ ((𝔸(σ; S) ↘ S) ⁻¹ᵁ U).ι = f) : (𝔸(σ; S) ↘ S) ⁻¹ᵁ U ≤ f.opensRange := by
      subst hf
      rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    exact this _ hE
  have htop : AffineSpace.map σ U.ι ⁻¹ᵁ ((𝔸(σ; S) ↘ S) ⁻¹ᵁ U) = ⊤ := by
    rw [← hE, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have := Scheme.Hom.isIso_app (AffineSpace.map σ U.ι) _ hrange
  have hle : (⊤ : 𝔸(σ; U.toScheme).Opens) ≤
      AffineSpace.map σ U.ι ⁻¹ᵁ ((𝔸(σ; S) ↘ S) ⁻¹ᵁ U) := htop.ge
  let r := (AffineSpace.map σ U.ι).appLE ((𝔸(σ; S) ↘ S) ⁻¹ᵁ U) ⊤ hle
  have : IsIso r := by
    simp only [r, Scheme.Hom.appLE]
    rw [show homOfLE hle = eqToHom htop.symm from Subsingleton.elim _ _]
    infer_instance
  let e := asIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge)
  have key : r.hom.comp (comparisonApp S σ U) =
      (eval₂Hom ((𝔸(σ; U.toScheme) ↘ U.toScheme).appTop).hom
        (AffineSpace.coord U.toScheme)).comp (MvPolynomial.map e.hom.hom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have h₁ : (𝔸(σ; S) ↘ S).app U ≫ r =
          (AffineSpace.map σ U.ι ≫ (𝔸(σ; S) ↘ S)).appLE U ⊤ (by simp) := by
        rw [Scheme.Hom.comp_appLE]
      have h₂ : U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ (𝔸(σ; U.toScheme) ↘ U.toScheme).appTop =
          ((𝔸(σ; U.toScheme) ↘ U.toScheme) ≫ U.ι).appLE U ⊤ (by simp) := by
        rw [← appLE_top_top _ (Scheme.Hom.preimage_top _).ge, Scheme.Hom.appLE_comp_appLE]
      have h₃ (g₁ g₂ : 𝔸(σ; U.toScheme) ⟶ S) (hg : g₁ = g₂) (W : 𝔸(σ; U.toScheme).Opens)
          (e₁ : W ≤ g₁ ⁻¹ᵁ U) (e₂ : W ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U W e₁ = g₂.appLE U W e₂ := by
        subst hg; rfl
      have := congr($(h₁.trans ((h₃ _ _ (AffineSpace.map_over U.ι) _ _ _).trans h₂.symm)).hom a)
      simp only [comparisonApp, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C,
        eval₂Hom_C]
      exact this
    · simp only [comparisonApp, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X',
        MvPolynomial.map_X]
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, appLE_top_top,
        AffineSpace.map_appTop_coord]
  have hm : Function.Bijective (MvPolynomial.map (σ := σ) e.hom.hom) :=
    (MvPolynomial.mapEquiv σ e.commRingCatIsoToRingEquiv).bijective
  refine (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso r) _).mp ?_
  rw [← RingHom.coe_comp, key, RingHom.coe_comp]
  exact (bijective_eval₂Hom_coord σ U.toScheme).comp hm

/-- The comparison map is locally injective: over an affine open it is injective. -/
instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology S) (comparison S σ) where
  equalizerSieve_mem {U} x y h := by
    intro p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hp U.unop.2
    refine ⟨V, homOfLE hVU, ?_, hpV⟩
    apply (comparisonApp_bijective S σ hV).injective
    have hn := (comparison S σ).naturality (homOfLE hVU).op
    exact (congr($hn x)).trans ((congrArg _ h).trans (congr($hn y)).symm)

/-- The comparison map is locally surjective: over an affine open it is surjective. -/
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S) (comparison S σ) := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun U t p hp => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hp U.2
  obtain ⟨s, hs⟩ := (comparisonApp_bijective S σ hV).surjective
    ((𝔸(σ; S).presheaf.map (homOfLE ((𝔸(σ; S) ↘ S).preimage_mono hVU)).op).hom t)
  exact ⟨V, hVU, ⟨s, hs⟩, hpV⟩

/-- The comparison of sheaves `𝒪_S[T_i] ⟶ π_* 𝒪_{𝔸(σ; S)}` induced by `comparison`. -/
abbrev comparisonSheafHom :
    (polynomialSheafification S σ).right ⟶ (FPAlgebraSheaf.polynomialAlgebra S σ).right :=
  Sites.FreeAlgebra.freeAlgebraSheafDesc _ S.sheaf _ (polynomialVariables S σ)
    (FPAlgebraSheaf.polynomialAlgebra S σ).hom (coordinates S σ)

/-- The comparison of sheaves extends the comparison of presheaves. -/
theorem toSheafify_comparisonSheafHom :
    toSheafify (Opens.grothendieckTopology S) (polynomialPresheaf S σ) ≫
      (comparisonSheafHom S σ).hom = comparison S σ :=
  Sites.FreeAlgebra.freeAlgebraSheafDesc_spec _ _ _ _ _ _

/-- The comparison of sheaves is an isomorphism, since the comparison of presheaves is locally
bijective. -/
instance isIso_comparisonSheafHom : IsIso (comparisonSheafHom S σ) := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S)
      (toSheafify (Opens.grothendieckTopology S) (polynomialPresheaf S σ)) :=
    GrothendieckTopology.W.isLocallySurjective
      ((Opens.grothendieckTopology S).W_toSheafify (polynomialPresheaf S σ))
  refine (Sheaf.isLocallyBijective_iff_isIso (A := CommRingCat.{u})
    (comparisonSheafHom S σ)).mp ⟨?_, ?_⟩
  · exact @Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ _
      (Opens.grothendieckTopology S) _ _ _ _ _ _ _ _ _ _ _ _ (toSheafify_comparisonSheafHom S σ)
      inferInstance this
  · exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (toSheafify_comparisonSheafHom S σ)

/-- **The polynomial algebra sheaf `𝒪_S[T_i]` is the sheaf associated to the presheaf
`U ↦ 𝒪_S(U)[T_i]`**, as sheaves of commutative `𝒪_S`-algebras: the sheafification of that
presheaf, with structure morphism the inclusion of constants, is isomorphic to
`Stacks.FPAlgebraSheaf.polynomialAlgebra S σ` by the map sending `T_i` to the `i`-th
coordinate. -/
def sheafificationIso :
    polynomialSheafification S σ ≅ FPAlgebraSheaf.polynomialAlgebra S σ :=
  Under.isoMk (@asIso _ _ _ _ (comparisonSheafHom S σ) (isIso_comparisonSheafHom S σ))
    (Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _)

/-- Over an affine open `U`, the sections of `𝒪_S[T_i]` are the polynomial ring
`𝒪_S(U)[T_i]`: the unit of the sheafification is bijective there. -/
theorem bijective_toSheafify_app {U : S.Opens} (hU : IsAffineOpen U) :
    Function.Bijective
      ((toSheafify (Opens.grothendieckTopology S) (polynomialPresheaf S σ)).app (op U)) := by
  have h : (toSheafify (Opens.grothendieckTopology S) (polynomialPresheaf S σ)).app (op U) ≫
      (comparisonSheafHom S σ).hom.app (op U) = (comparison S σ).app (op U) :=
    congr($(toSheafify_comparisonSheafHom S σ).app (op U))
  have hc : Function.Bijective ((comparison S σ).app (op U)) := comparisonApp_bijective S σ hU
  rw [← h] at hc
  let e := (sheafToPresheaf _ _).mapIso
    (@asIso _ _ _ _ (comparisonSheafHom S σ) (isIso_comparisonSheafHom S σ))
  exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
    (e.app (op U)).hom) _).mp hc

/-- The sheaf of `𝒪_S`-algebras `𝒪_S[T_i]` associated to `U ↦ 𝒪_S(U)[T_i]` is quasi-coherent,
being isomorphic to the direct image of the structure sheaf along the affine morphism
`𝔸(σ; S) ⟶ S`. -/
instance isQuasicoherent_polynomialSheafification :
    AlgebraSheaf.IsQuasicoherent (polynomialSheafification S σ) :=
  AlgebraSheaf.isQuasicoherent_of_iso (sheafificationIso S σ).symm
    (isQuasicoherent_pushforwardAlgebra (𝔸(σ; S) ↘ S))

/-! ### Affine space as a relative spectrum -/

/-- Affine space over a scheme `S` in the variables `T_i`, `i ∈ σ`: the relative spectrum
`Spec_S(𝒪_S[T_i])` of the quasi-coherent sheaf of `𝒪_S`-algebras `𝒪_S[T_i]`, the sheaf
associated to `U ↦ 𝒪_S(U)[T_i]`, as a scheme over `S`. -/
def affineSpace : Over S :=
  Over.mk (relativeSpecToBase (polynomialSheafification S σ))

/-- Affine space over `S` is Mathlib's `𝔸(σ; S)`, the base change `S ×_ℤ 𝔸^σ_ℤ`, over `S`. -/
def affineSpaceIso : Over.mk (𝔸(σ; S) ↘ S) ≅ affineSpace S σ :=
  relativeSpecIsoOfAlgebraIso (𝔸(σ; S) ↘ S) (polynomialSheafification S σ)
    (sheafificationIso S σ).symm

/-- **Affine `n`-space over a scheme.** For a scheme `S` and an integer `n ≥ 0`, affine `n`-space
`𝐀ⁿ_S = Spec_S(𝒪_S[T_1, …, T_n])` over `S` is the relative spectrum of the quasi-coherent sheaf
of `𝒪_S`-algebras `𝒪_S[T_1, …, T_n]`, as a scheme over `S`. For `S = Spec R` this is affine
`n`-space `𝐀ⁿ_R` over `R`.

Here `𝒪_S[T_1, …, T_n]` is the sheaf associated to the presheaf `U ↦ 𝒪_S(U)[T_1, …, T_n]`,
whose sections over an affine open `U` are `𝒪_S(U)[T_1, …, T_n]`
(`Stacks.AffineSpace.bijective_toSheafify_app`), and the result is Mathlib's `𝔸(n; S)` over `S`
by `Stacks.AffineSpace.affineSpaceIso`. -/
@[stacks 01M0 "affine n-space over S, the relative spectrum of the polynomial algebra \
O_S[T_1, ..., T_n], as a scheme over S", ega "IV 5.5.5"]
abbrev affineNSpace (n : ℕ) : Over S :=
  affineSpace S (ULift.{u} (Fin n))

/-- Over an affine base, affine space is the spectrum of the polynomial ring:
`𝐀^σ_R = Spec R[T_i]` over `Spec R`. -/
def affineSpaceSpecIso (R : CommRingCat.{u}) :
    affineSpace (Spec R) σ ≅
      Over.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := σ) (R := R)))) :=
  (affineSpaceIso (Spec R) σ).symm ≪≫ Over.isoMk (AffineSpace.SpecIso σ R) (by
    simp only [Over.mk_hom]
    rw [← Iso.eq_inv_comp, AffineSpace.SpecIso_inv_over])

end Stacks.AffineSpace

end
