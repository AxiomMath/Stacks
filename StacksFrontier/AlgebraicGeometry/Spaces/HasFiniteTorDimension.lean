module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChangeSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.Homology.TorAmplitude.Module

/-!
# Morphisms of algebraic spaces of finite Tor dimension

A morphism `g : Y' ⟶ Y` of algebraic spaces has finite Tor dimension (More on Morphisms of
Spaces) when `𝒪_{Y'}` has finite Tor dimension over `g^{-1}𝒪_Y`. We use its étale-local form: for
every commutative square of affine étale charts `V' ⟶ Y'`, `V ⟶ Y` over `g`, the ring map
`Γ(V, 𝒪) ⟶ Γ(V', 𝒪)` has finite Tor dimension. This is the hypothesis under which case (3) of
Stacks 0DKI holds, and the ring-level hypothesis of Stacks 0E4S (2).

## Main definitions

* `AlgebraicGeometry.Space.HasFiniteTorDimension`: a morphism of algebraic spaces of finite Tor
  dimension, in étale-local form.

## Main results

* `AlgebraicGeometry.Space.HasFiniteTorDimension.of_isFlat`: a flat morphism has finite Tor
  dimension (Tor dimension `0`).
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of algebraic spaces of finite Tor dimension**, in étale-local form: for every
commutative square `V' ⟶ V` over `g : Y' ⟶ Y` of affine étale charts `V' ⟶ Y'`, `V ⟶ Y`, the
ring map `Γ(V, 𝒪) ⟶ Γ(V', 𝒪)` has finite Tor dimension. -/
structure HasFiniteTorDimension {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) : Prop where
  /-- The ring maps of the affine étale chart squares over `g` have finite Tor dimension. -/
  hasFiniteTorDimensionRingHom :
    ∀ (V V' : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (g₀ : V' ⟶ V), IsEtale B S hS b.hom → IsEtale B S hS c.hom →
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g →
      HasFiniteTorDimensionRingHom (representedAffineRingCatHom B S hS g₀).hom

/-- A flat ring map has finite Tor dimension, with Tor amplitude in `[0, 0]`. -/
theorem hasFiniteTorDimensionRingHom_of_flat {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (hφ : φ.Flat) : HasFiniteTorDimensionRingHom φ := by
  let := φ.toAlgebra
  refine ⟨0, 0, (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
    R _ 0 0).2 ?_⟩
  refine StacksDraft.TorAmplitude.hasFlatRepresentative_of_iso.{u, u}
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app (ModuleCat.of R R'))
    ((StacksDraft.TorAmplitude.hasFlatRepresentative_single_zero_iff.{u, u}
      (ModuleCat.of R R')).2 hφ)

/-- **A flat morphism of algebraic spaces has finite Tor dimension.** -/
theorem HasFiniteTorDimension.of_isFlat {Y Y' : AlgebraicSpaces B S hS} {g : Y' ⟶ Y}
    (hg : IsFlat B S hS g.hom) : HasFiniteTorDimension g where
  hasFiniteTorDimensionRingHom V V' _ _ b c g₀ hb hc h := by
    have hfl : Flat ((BigFppfOver.toScheme B S hS).map g₀) :=
      hg V' V c.hom b.hom g₀ ((isEtale_iff_presheaf_of_yoneda B S hS c.hom).1 hc)
        ((isEtale_iff_presheaf_of_yoneda B S hS b.hom).1 hb) (congrArg (fun k => k.hom) h)
    exact hasFiniteTorDimensionRingHom_of_flat _
      (HasRingHomProperty.appTop (P := @Flat) _ hfl)

end AlgebraicGeometry.Space

end
