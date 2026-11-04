module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism

/-!
# Morphisms inducing an isomorphism on one local ring

A morphism locally of finite presentation whose map of local rings at a point `x` is an
isomorphism is an open immersion on an open neighbourhood of `x`.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_of_isIso_stalkMap`: a morphism locally of finite
  presentation whose stalk map at `x` is an isomorphism is an open immersion near `x`.
* `AlgebraicGeometry.exists_isOpenImmersion_of_etale_of_isIso_stalkMap`: the same for an étale
  morphism.
* `AlgebraicGeometry.isLocalIso_of_forall_isIso_stalkMap`: a morphism locally of finite
  presentation all of whose stalk maps are isomorphisms is a local isomorphism.

## References

* [Stacks Project, Tag 00QS](https://stacks.math.columbia.edu/tag/00QS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **An isomorphism on one local ring spreads out.** If `f : X ⟶ S` is locally of finite
presentation and the induced map `𝒪_{S, f x} ⟶ 𝒪_{X, x}` is an isomorphism, then `f` restricts
to an open immersion on an open neighbourhood of `x`. -/
theorem exists_isOpenImmersion_of_isIso_stalkMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) (hstalk : IsIso (f.stalkMap x)) :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hfxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfxV (V.2.preimage f.continuous)
  have hfp := f.finitePresentation_appLE hV hU hUV
  algebraize [(f.appLE V U hUV).hom]
  have hpq : (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal =
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.comap (algebraMap Γ(S, V) Γ(X, U)) :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU).1).symm
  have := IsScalarTower.of_algebraMap_eq
    (R := Γ(S, V)) (S := Γ(X, U))
    (A := Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) fun _ ↦ rfl
  have hbij : Function.Bijective (Localization.localRingHom
      (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      (f.appLE V U hUV).hom hpq) := by
    refine (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom _)).mp ?_
    exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f V hV U hU hUV hxU)).mp hstalk
  have hcomm : ∀ r : Γ(S, V), Localization.localRingHom
      (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      (f.appLE V U hUV).hom hpq
        (algebraMap Γ(S, V) (Localization.AtPrime
          (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal) r) =
      algebraMap Γ(S, V) (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) r := by
    intro r
    exact Localization.localRingHom_to_map _ _ _ _ _
  let eloc : Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ≃ₐ[Γ(S, V)]
      Localization.AtPrime (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal :=
    (AlgEquiv.ofBijective
      ({ Localization.localRingHom _ _ (f.appLE V U hUV).hom hpq with
          commutes' := hcomm } :
        Localization.AtPrime (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal →ₐ[Γ(S, V)]
          Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) hbij).symm
  obtain ⟨g, hg, g', -, ⟨ψ⟩⟩ :=
    Algebra.FinitePresentation.exists_algEquiv_localizationAway_of_algEquiv_atPrime
      (R := Γ(S, V)) (S := Γ(X, U)) (S' := Γ(S, V))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)
      (Localization.AtPrime (hV.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal) eloc
  have hxg : x ∈ X.basicOpen g := by
    let _ := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact (Scheme.mem_basicOpen X g x hxU).mpr
      ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (⟨x, hxU⟩ : U))
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal g).mpr hg)
  have := hU.isLocalization_basicOpen g
  have := hV.isLocalization_basicOpen g'
  have htower := IsScalarTower.of_algebraMap_eq
    (R := Γ(S, V)) (S := Γ(X, U)) (A := Localization.Away g) fun _ ↦ rfl
  let α : Localization.Away g ≃ₐ[Γ(X, U)] Γ(X, X.basicOpen g) :=
    IsLocalization.algEquiv (Submonoid.powers g) _ _
  let β : Localization.Away g' ≃ₐ[Γ(S, V)] Γ(S, S.basicOpen g') :=
    IsLocalization.algEquiv (Submonoid.powers g') _ _
  have hunit : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g)
      (algebraMap Γ(S, V) Γ(X, U) g')) := by
    have h1 : IsUnit (algebraMap Γ(S, V) (Localization.Away g') g') :=
      IsLocalization.Away.algebraMap_isUnit g'
    rw [← ψ.commutes g'] at h1
    have h2 := (h1.map ψ.symm).map α
    rwa [ψ.symm_apply_apply, IsScalarTower.algebraMap_apply Γ(S, V) Γ(X, U)
      (Localization.Away g), α.commutes] at h2
  have hle : X.basicOpen g ≤ f ⁻¹ᵁ S.basicOpen g' := by
    have h1 : X.basicOpen (f.appLE V U hUV g') = U ⊓ f ⁻¹ᵁ S.basicOpen g' :=
      Scheme.basicOpen_appLE f U V hUV g'
    have h2 : X.basicOpen (algebraMap Γ(X, U) Γ(X, X.basicOpen g)
        (f.appLE V U hUV g')) = X.basicOpen g := X.basicOpen_of_isUnit hunit
    rw [show algebraMap Γ(X, U) Γ(X, X.basicOpen g) (f.appLE V U hUV g') =
      X.presheaf.map (homOfLE (X.basicOpen_le g)).op (f.appLE V U hUV g') from rfl,
      Scheme.basicOpen_res, h1] at h2
    exact h2.ge.trans (le_trans inf_le_right inf_le_right)
  let Θ : Γ(X, X.basicOpen g) ≃+* Γ(S, S.basicOpen g') :=
    (α.toRingEquiv.symm.trans ψ.toRingEquiv).trans β.toRingEquiv
  have hΘ : (Θ : Γ(X, X.basicOpen g) →+* Γ(S, S.basicOpen g')).comp
      (f.appLE (S.basicOpen g') (X.basicOpen g) hle).hom = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g') ?_
    ext r
    have happ : (f.appLE (S.basicOpen g') (X.basicOpen g) hle).hom
        (algebraMap Γ(S, V) Γ(S, S.basicOpen g') r) =
        algebraMap Γ(X, U) Γ(X, X.basicOpen g) (algebraMap Γ(S, V) Γ(X, U) r) := by
      have h1 : S.presheaf.map (homOfLE (S.basicOpen_le g')).op ≫
          f.appLE (S.basicOpen g') (X.basicOpen g) hle =
          f.appLE V (X.basicOpen g) ((X.basicOpen_le g).trans hUV) :=
        Scheme.Hom.map_appLE f hle _
      have h2 : f.appLE V U hUV ≫ X.presheaf.map (homOfLE (X.basicOpen_le g)).op =
          f.appLE V (X.basicOpen g) ((X.basicOpen_le g).trans hUV) :=
        Scheme.Hom.appLE_map f hUV _
      exact congr($(h1.trans h2.symm) r)
    simp only [RingHom.coe_comp, Function.comp_apply, happ, RingHom.id_apply]
    rw [show (Θ : Γ(X, X.basicOpen g) →+* Γ(S, S.basicOpen g'))
        (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (algebraMap Γ(S, V) Γ(X, U) r)) =
        β (ψ (α.symm (algebraMap Γ(X, U) Γ(X, X.basicOpen g)
          (algebraMap Γ(S, V) Γ(X, U) r)))) from rfl,
      α.symm.commutes, ← IsScalarTower.algebraMap_apply, ψ.commutes, β.commutes]
  have hbij' : Function.Bijective (f.appLE (S.basicOpen g') (X.basicOpen g) hle).hom := by
    have hfun : ⇑(f.appLE (S.basicOpen g') (X.basicOpen g) hle).hom = ⇑Θ.symm := by
      funext y
      exact (Θ.symm_apply_eq.mpr (RingHom.congr_fun hΘ y).symm).symm
    exact hfun ▸ Θ.symm.bijective
  have : IsIso (f.appLE (S.basicOpen g') (X.basicOpen g) hle) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij'
  have : IsAffine (X.basicOpen g).toScheme := hU.basicOpen g
  have : IsAffine (S.basicOpen g').toScheme := hV.basicOpen g'
  have : IsIso (f.resLE (S.basicOpen g') (X.basicOpen g) hle).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    infer_instance
  have : IsIso (f.resLE (S.basicOpen g') (X.basicOpen g) hle ≫
      (S.basicOpen g').toScheme.toSpecΓ) := by
    rw [Scheme.toSpecΓ_naturality]
    infer_instance
  have : IsIso (f.resLE (S.basicOpen g') (X.basicOpen g) hle) :=
    IsIso.of_isIso_comp_right _ (S.basicOpen g').toScheme.toSpecΓ
  refine ⟨X.basicOpen g, hxg, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hle]
  infer_instance

/-- An étale morphism whose map of local rings at `x` is an isomorphism is an open immersion on
an open neighbourhood of `x`. -/
theorem exists_isOpenImmersion_of_etale_of_isIso_stalkMap {X S : Scheme.{u}} (f : X ⟶ S)
    [Etale f] (x : X) (hstalk : IsIso (f.stalkMap x)) :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) :=
  exists_isOpenImmersion_of_isIso_stalkMap f x hstalk

/-- A morphism locally of finite presentation which is an isomorphism on all local rings is a
local isomorphism, that is, it is source-locally an open immersion. -/
theorem isLocalIso_of_forall_isIso_stalkMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (hstalk : ∀ x : X, IsIso (f.stalkMap x)) :
    IsLocalIso f :=
  ⟨fun x ↦ exists_isOpenImmersion_of_isIso_stalkMap f x (hstalk x)⟩

end AlgebraicGeometry

end
