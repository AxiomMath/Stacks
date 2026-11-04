module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Residue field extensions along étale morphisms are étale

Let `f : X ⟶ Y` be an étale morphism of schemes and `x` a point of `X`. The extension of
residue fields `κ(f(x)) ⟶ κ(x)` is finite and separable, so the induced morphism
`Spec κ(x) ⟶ Spec κ(f(x))` is étale. This file records that fact, first for local algebras,
then for morphisms of schemes, and finally for the morphism of residue-field points of the big
fppf site induced by a morphism of the site, both as a morphism of schemes and as a morphism of
algebraic spaces.

## Main results

* `Algebra.Etale.residueField_of_formallyUnramified`: for a local homomorphism `R ⟶ A` of
  local rings which is essentially of finite type and formally unramified, the residue field
  extension is étale.
* `AlgebraicGeometry.etale_specMap_residueFieldMap`: for an étale morphism of schemes `f` and
  a point `x`, the morphism `Spec κ(x) ⟶ Spec κ(f(x))` is étale.
* `AlgebraicGeometry.Space.etale_residueFieldObjectMap`: the same for the morphism of
  residue-field points of the big fppf site induced by a morphism with étale underlying
  morphism of schemes.
* `AlgebraicGeometry.Space.isEtale_schemeSpaceMap_residueFieldObjectMap`: the induced morphism
  of represented algebraic spaces is étale.

## Implementation notes

The residue field extension is essentially of finite type, being a quotient of the stalk map,
and separable by Mathlib's instance for formally unramified morphisms locally of finite type.
A formally unramified algebra essentially of finite type over a field is finite
(`Algebra.FormallyUnramified.finite_of_free`), and a finite separable field extension is
formally étale (`Algebra.FormallyEtale.of_isSeparable`) and of finite presentation, hence
étale.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

/-- **The residue field extension of a formally unramified local homomorphism is étale.** Let
`R ⟶ A` be a local homomorphism of local rings which is essentially of finite type and formally
unramified. Then `κ(A)` is an étale algebra over `κ(R)`: it is separable, and finite because a
formally unramified algebra essentially of finite type over a field is finite. -/
@[ega "0 19.10.3" "partial",
  ega "0 21.7.4" "b ⇒ c",
  ega "IV 17.4.1" "partial",
  ega "IV 18.8.6" "partial", sga "1 I 3.1" "(ii)"]
theorem Algebra.Etale.residueField_of_formallyUnramified (R A : Type*) [CommRing R]
    [CommRing A] [IsLocalRing R] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A] :
    Algebra.Etale (ResidueField R) (ResidueField A) := by
  have : Algebra.EssFiniteType R (ResidueField A) :=
    inferInstanceAs (Algebra.EssFiniteType R (A ⧸ maximalIdeal A))
  have : Algebra.EssFiniteType (ResidueField R) (ResidueField A) :=
    Algebra.EssFiniteType.of_comp R _ _
  have : Algebra.FormallyEtale (ResidueField R) (ResidueField A) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Module.Finite (ResidueField R) (ResidueField A) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.FinitePresentation (ResidueField R) (ResidueField A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

namespace AlgebraicGeometry

/-- **The residue field extension of an étale morphism is étale.** For an étale morphism of
schemes `f : X ⟶ Y` and a point `x` of `X`, the morphism `Spec κ(x) ⟶ Spec κ(f(x))` induced by
the residue field extension is étale. -/
alias etale_specMap_residueFieldMap := AlgebraicGeometry.etale_residueFieldMap

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of residue-field points induced by an étale morphism is étale.** For a
morphism `f : T ⟶ Q` of the big fppf site over `S` whose underlying morphism of schemes is
étale and a point `p` of `T`, the morphism `Spec κ(p) ⟶ Spec κ(f(p))` of residue-field points of
the site has étale underlying morphism of schemes. -/
theorem etale_residueFieldObjectMap (T Q : BigFppfOver B S hS) (f : T ⟶ Q)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f)) (p : T.left.1) :
    Etale ((BigFppfOver.toScheme B S hS).map (residueFieldObjectMap B S hS T Q f p)) := by
  have : Etale f.left.1 := hf
  exact etale_specMap_residueFieldMap f.left.1 p

/-- **The morphism of represented algebraic spaces induced on residue-field points by an étale
morphism is étale.** -/
theorem isEtale_schemeSpaceMap_residueFieldObjectMap (T Q : BigFppfOver B S hS) (f : T ⟶ Q)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f)) (p : T.left.1) :
    IsEtale B S hS (schemeSpaceMap (residueFieldObjectMap B S hS T Q f p)).hom :=
  isEtale_schemeSpaceMap B S hS _ _ (etale_residueFieldObjectMap B S hS T Q f hf p)

end Space

end AlgebraicGeometry

end
