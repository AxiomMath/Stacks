module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGammaFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationQcqs

/-!
# Criteria for the structure map `𝒪_T ⟶ h_* 𝒪_X` to be an isomorphism

Three criteria for invertibility of the structure map `h^♯ : 𝒪_T ⟶ h_* 𝒪_X` of a morphism
`h : X ⟶ T` of algebraic spaces (Stacks 03G8), used for Stacks 0AYI.

* A morphism of sheaves of commutative rings on a site which is bijective on the sections over
  the members of a covering family of every object is an isomorphism.
* For a proper `h` with affine target, `h^♯` is an isomorphism as soon as it is bijective on
  global sections.  The normalization `T'` of `T` in `X` (Stacks 0822) is affine over `T`, hence
  affine, and it has the global functions of `X` (Stacks 0A19, clause (3)); so `T' ⟶ T` is a
  morphism of affine algebraic spaces which is bijective on global functions, hence an
  isomorphism, and then `h^♯` is the isomorphism `𝒪_{T'} ⟶ h'_* 𝒪_X` of Stacks 0A19.
* The commutative algebra behind Stacks 0AB1: an integral extension of a normal domain `A`
  which embeds into the fraction field of `A` compatibly with `A` is `A` itself.

## Main results

* `Stacks.Sites.isIso_of_locallyBijective_app`: the first criterion.
* `AlgebraicGeometry.Space.isIso_fSharp_of_isIso_pushforwardAlgebraMap_overHomToId`: `h^♯` is an
  isomorphism when the direct-image map of `h` over `T` is.
* `AlgebraicGeometry.Space.isIso_fSharp_of_bijective_globalFunctionsMap`: the second criterion.
* `Stacks.bijective_of_isIntegral_of_injective_comp_eq_algebraMap`: the third.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites

/-- **A morphism of sheaves of commutative rings which is bijective on the sections over the
members of a covering of every object is an isomorphism.**  It is locally injective and locally
surjective, and a locally bijective morphism of sheaves is an isomorphism. -/
theorem isIso_of_locallyBijective_app {C : Type*} [Category C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget CommRingCat.{u})] {F G : Sheaf J CommRingCat.{u}} (i : F ⟶ G)
    (hi : ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f → Function.Bijective (i.hom.app (op V)).hom) :
    IsIso i := by
  have hmono : Mono i := mono_of_locallyInjective_app J i fun U => by
    obtain ⟨R, hR, h⟩ := hi U
    exact ⟨R, hR, fun V f hf => (h V f hf).1⟩
  refine (Sheaf.isLocallyBijective_iff_isIso _).mp
    ⟨Presheaf.isLocallyInjective_of_injective J _ (injective_app_of_mono J i), ⟨fun {U} x => ?_⟩⟩
  obtain ⟨R, hR, h⟩ := hi U
  exact J.superset_covering ((Sieve.generate_le_iff _ _).mpr fun V f hf => (h V f hf).2 _) hR

end Stacks.Sites

namespace Stacks

/-- **An integral extension of a normal domain which embeds into its fraction field compatibly
with the domain is trivial.**  Let `A` be an integrally closed domain with fraction field `L`, and
let `ι : A ⟶ N` be an integral ring map admitting an injective ring map `φ : N ⟶ L` with
`φ ∘ ι = A ⟶ L`.  Then `ι` is bijective.

Every element of `N` maps to an element of `L` integral over `A`, hence to an element of `A`
because `A` is integrally closed; injectivity of `φ` brings it back.  This is the commutative
algebra of [Stacks, Tag 0AB1]. -/
theorem bijective_of_isIntegral_of_injective_comp_eq_algebraMap {A N L : Type*} [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [CommRing N] [CommRing L] [Algebra A L] [IsFractionRing A L]
    (ι : A →+* N) (hι : ι.IsIntegral) (φ : N →+* L) (hφ : Function.Injective φ)
    (hcomp : φ.comp ι = algebraMap A L) : Function.Bijective ι := by
  refine ⟨fun a b hab => IsFractionRing.injective A L ?_, fun n => ?_⟩
  · rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, hab]
  · obtain ⟨p, hpm, hp⟩ := hι n
    have hint : IsIntegral A (φ n) := by
      refine ⟨p, hpm, ?_⟩
      rw [← hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨a, hφ ?_⟩
    rw [← RingHom.comp_apply, hcomp, ha]

end Stacks

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The structure map of `q : Y ⟶ T` is an isomorphism when the direct-image map of `q` over
`T` is.**  The direct-image map of `q` over `T`, read through the identification of the direct
image along the identity of `T` with `𝒪_T`, is the structure-algebra map of `q_* 𝒪_Y`
(`AlgebraicGeometry.Space.pushforwardAlgebraMap_overHomToId_algebraMap`), which is the structure
map of Stacks 03G8. -/
theorem isIso_fSharp_of_isIso_pushforwardAlgebraMap_overHomToId {T Y : AlgebraicSpaces B S hS}
    (q : Y ⟶ T) [IsIso (pushforwardAlgebraMap B S hS (overHomToId B S hS q))] :
    IsIso (smallEtaleRingedToposHom B S hS q).fSharp := by
  let e := asIso (pushforwardAlgebraMap B S hS (overHomToId B S hS q))
  have hbij : ∀ U : (SmallEtale B S hS T.1)ᵒᵖ,
      Function.Bijective ((smallEtaleRingedToposHom B S hS q).fSharp.hom.app U) := by
    intro U
    have hb : Function.Bijective (e.hom.right.hom.app U) :=
      ⟨Function.LeftInverse.injective (AlgebraSheaf.iso_inv_right_app_hom_right_app e U),
        Function.RightInverse.surjective (AlgebraSheaf.iso_inv_right_app_hom_right_app e.symm U)⟩
    have heq : ⇑((smallEtaleRingedToposHom B S hS q).fSharp.hom.app U) =
        ⇑(e.hom.right.hom.app U) ∘
          (pushforwardAlgebra B S hS (idAffineOver B S hS T).obj).algebraMap U := by
      funext r
      exact (pushforwardAlgebraMap_overHomToId_algebraMap B S hS q U r).symm
    rw [heq]
    exact hb.comp (bijective_pushforwardAlgebra_id_algebraMap B S hS _ U)
  exact isIso_commRingSheafHom_of_bijective_app _ hbij

/-- **For a proper morphism to an affine algebraic space, the structure map is an isomorphism as
soon as it is bijective on global functions.**  Let `h : X ⟶ T` be proper with `T` affine, and
suppose the pullback `Γ(T, 𝒪_T) ⟶ Γ(X, 𝒪_X)` is bijective.  Then `𝒪_T ⟶ h_* 𝒪_X` is an
isomorphism.

Let `X ⟶ T' ⟶ T` be the factorization through the normalization of `T` in `X` (Stacks 0822).
`T'` is affine over `T`, hence affine; `𝒪_{T'} ⟶ h'_* 𝒪_X` is an isomorphism (Stacks 0A19,
clause (3)), so `Γ(T') ⟶ Γ(X)` is bijective, and therefore so is `Γ(T) ⟶ Γ(T')`; a morphism of
affine algebraic spaces bijective on global functions is an isomorphism.  The direct-image map of
`h` over `T` is then the composite of the isomorphism of Stacks 0A0Q with the direct-image map of
that isomorphism. -/
theorem isIso_fSharp_of_bijective_globalFunctionsMap {X T : AlgebraicSpaces B S hS} (h : X ⟶ T)
    (hh : IsProper B S hS h.hom) (hT : IsAffineSpace B S hS T.obj)
    (hbij : Function.Bijective (globalFunctionsMap B S hS h)) :
    IsIso (smallEtaleRingedToposHom B S hS h).fSharp := by
  obtain ⟨hqc, hqs⟩ := isQuasiCompact_isQuasiSeparated_of_isProper B S hS h hh
  let π := normalizationInQcqsHom B S hS h hqc hqs
  let h' := toNormalizationInQcqs h hqc hqs
  have hfac : h' ≫ π = h := toNormalizationInQcqs_comp h hqc hqs
  have : IsIso (smallEtaleRingedToposHom B S hS h').fSharp :=
    isIso_fSharp_toNormalizationInQcqs h hqc hqs hh.2.2
  have hT' : IsAffineSpace B S hS (normalizationInQcqs B S hS h hqc hqs).obj :=
    (isAffineHom_normalizationInQcqsHom B S hS h hqc hqs).isAffineSpace_source hT
  have hbij' : Function.Bijective (globalFunctionsMap B S hS h') :=
    bijective_globalFunctionsMap_of_isIso_fSharp h'
  have hπ : Function.Bijective (globalFunctionsMap B S hS π) := by
    have hcomp : globalFunctionsMap B S hS h =
        (globalFunctionsMap B S hS h').comp (globalFunctionsMap B S hS π) := by
      rw [← globalFunctionsMap_comp, hfac]
    rw [hcomp, RingHom.coe_comp] at hbij
    refine ⟨Function.Injective.of_comp hbij.1, fun y => ?_⟩
    obtain ⟨x, hx⟩ := hbij.2 (globalFunctionsMap B S hS h' y)
    exact ⟨x, hbij'.1 hx⟩
  have hπiso : IsIso π := isIso_of_bijective_globalFunctionsMap B S hS hT' hT π hπ
  let πinv := inv π
  have hπ₁ : π ≫ πinv = 𝟙 _ := IsIso.hom_inv_id π
  have hπ₂ : πinv ≫ π = 𝟙 _ := IsIso.inv_hom_id π
  -- the direct-image map of `π` over `T` is invertible
  let N := normalizationInQcqsAffineOver B S hS h hqc hqs
  let I := idAffineOver B S hS T
  let Φ : N.obj ⟶ I.obj := Over.homMk π (Category.comp_id _)
  let Φinv : I.obj ⟶ N.obj := Over.homMk πinv hπ₂
  have hΦ : Φ ≫ Φinv = 𝟙 _ := Over.OverMorphism.ext hπ₁
  have hΦ' : Φinv ≫ Φ = 𝟙 _ := Over.OverMorphism.ext hπ₂
  have : IsIso (pushforwardAlgebraMap B S hS Φ) :=
    ⟨pushforwardAlgebraMap B S hS Φinv,
      by rw [← pushforwardAlgebraMap_comp, hΦ', pushforwardAlgebraMap_id],
      by rw [← pushforwardAlgebraMap_comp, hΦ, pushforwardAlgebraMap_id]⟩
  have := isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed h hqc hqs
    hh.2.2
  have hover : toNormalizationInQcqsOver h hqc hqs ≫ Φ = overHomToId B S hS h :=
    Over.OverMorphism.ext hfac
  have : IsIso (pushforwardAlgebraMap B S hS (overHomToId B S hS h)) := by
    rw [← hover, pushforwardAlgebraMap_comp]
    infer_instance
  exact isIso_fSharp_of_isIso_pushforwardAlgebraMap_overHomToId h

end AlgebraicGeometry.Space

end
