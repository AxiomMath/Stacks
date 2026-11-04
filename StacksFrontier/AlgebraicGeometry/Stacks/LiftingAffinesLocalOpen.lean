module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalReduction

/-!
# The open of an affine member cut out by the lifted chart, for Stacks 0CJV

For an affine open `T₀` of a scheme of the site with a morphism `κ : T₀ ⟶ Y_w` to the closed
subscheme `Y_w = Spec Γ(U'_w)/J` of an affine `U'_w`, a localization `λ : Γ(T₀) → S₁ ⧸ J S₁` away
from one element, compatible with `κ`, and `h' ∈ S₁` outside the prime of a point `y₀`, the
spectrum of `(S₁ ⧸ J S₁)[1/h']` is an étale neighbourhood of `y₀` in `T₀` lying over `Y_w`:
`AlgebraicGeometry.Stack.LiftingAffinesLocal.exists_awayQuotient_open`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.LiftingAffinesLocal

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The open `Spec (S₁ ⧸ J S₁)[1/h']` of `T₀`.** For a localization `λ : Γ(T₀) → S₁ ⧸ J S₁` away
from `d`, compatible with `T₀ ⟶ Y_w`, and `h'` outside the prime of a point `y₀` of `T₀` with
`d ∉ 𝔭_{y₀}`, the spectrum of `(S₁ ⧸ J S₁)[1/h']` maps to `T₀` by an étale morphism through
`y₀`, over `Y_w`. -/
theorem exists_awayQuotient_open {V Yw T₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Yw)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)] (c : Yw ⟶ V)
    (π : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⟶ Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤))
    (hπc : ((BigFppfOver.toScheme B S hS).map c).appTop = π) (hπ : Function.Surjective π.hom)
    (κ : T₀ ⟶ Yw) (S₁ : Type u) [CommRing S₁] [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁]
    (lam : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) →+*
      S₁ ⧸ (RingHom.ker π.hom).map (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁))
    (hlam : lam.comp ((BigFppfOver.toScheme B S hS).map κ).appTop.hom =
      BigFppfOver.quotientBaseMap π hπ S₁)
    (d : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤))
    (hloc : @IsLocalization.Away _ _ d (S₁ ⧸ (RingHom.ker π.hom).map
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁)) _ lam.toAlgebra)
    (y₀ : (BigFppfOver.toScheme B S hS).obj T₀)
    (hd : d ∉ (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal) (h' : S₁)
    (hh' : Ideal.Quotient.mk _ h' ∉
      (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal.map lam)
    (hcomp : (BigFppfOver.awayQuotientBase π hπ S₁ h').comp
        ((BigFppfOver.toScheme B S hS).map c).appTop.hom =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (BigFppfOver.AwayQuotient π S₁ h')) :
    ∃ m' : BigFppfOver.specObj V (BigFppfOver.AwayQuotient π S₁ h') ⟶ T₀,
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map m') ∧
      y₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map m') ∧
      m' ≫ κ = BigFppfOver.specObjHom c (BigFppfOver.awayQuotientBase π hπ S₁ h') hcomp := by
  have h0 : (BigFppfOver.awayQuotientOf π S₁ h' lam).comp
      ((BigFppfOver.toScheme B S hS).map (κ ≫ c)).appTop.hom =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) _ := by
    rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, hπc,
      ← RingHom.comp_assoc]
    exact BigFppfOver.awayQuotientOf_comp_comp π hπ S₁ h' lam _ hlam
  have hex := BigFppfOver.exists_isPrime_comap_awayQuotientOf π S₁ h' lam d hloc _ hd hh'
  have := hex.choose_spec.1
  exact ⟨BigFppfOver.specObjHom (κ ≫ c) (BigFppfOver.awayQuotientOf π S₁ h' lam) h0,
    (BigFppfOver.prop_specObjHom_iff @AlgebraicGeometry.Etale (κ ≫ c) _ h0).mpr
      (BigFppfOver.etale_awayQuotientOf π S₁ h' lam d hloc),
    BigFppfOver.mem_range_specObjHom (κ ≫ c) _ h0 y₀ hex.choose hex.choose_spec.2,
    BigFppfOver.specObjHom_comp_eq (κ ≫ c) _ h0 κ c _ hcomp
      (BigFppfOver.awayQuotientOf_comp π hπ S₁ h' lam _ hlam)⟩

end AlgebraicGeometry.Stack.LiftingAffinesLocal

end
