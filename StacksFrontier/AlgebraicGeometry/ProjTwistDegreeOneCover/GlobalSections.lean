module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjShiftedSectionModule
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic

/-!
# Homogeneous elements as global sections of the twists on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded `S`-module and
`X = Proj S`, and assume `X` is covered by the standard opens `D₊(f)` of the degree-one
elements. A homogeneous element of `M` of degree `n` is a degree-zero element of the shift
`M(n)`, hence gives a global section of `M(n)~`; transporting along the isomorphism
`M̃(n) = M̃ ⊗_{𝒪_X} 𝒪_X(n) ≅ M(n)~` gives the canonical map

`M_n ⟶ Γ(X, M̃(n))`.

The two maps differ by an isomorphism of sheaves, so each is bijective exactly when the other
is.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistedModuleGlobalSections`: the group
  `Γ(X, M̃(n))` of global sections of the `n`-th twist of `M̃`.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.degreeNToTwistedGlobalSections`: the
  canonical map `M_n ⟶ Γ(X, M̃(n))`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.bijective_moduleTwistIso_inv_app_top`: the
  isomorphism `M(n)~ ≅ M̃(n)` is bijective on global sections.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover`
  `.bijective_degreeNToTwistedGlobalSections_iff`: the canonical map `M_n ⟶ Γ(X, M̃(n))` is
  bijective if and only if the canonical map `M_n ⟶ Γ(X, M(n)~)` is.

## Implementation notes

Evaluation at an open is the functor `CategoryTheory.SheafOfModules.evaluation`, so an
isomorphism of sheaves of modules is carried to an isomorphism of modules of sections by
`CategoryTheory.Functor.mapIso`; that is how bijectivity on global sections is obtained,
the twist `M̃(n)` being a sheafified tensor product whose sections carry no description.

## References

* [Stacks Project, Tag 0AG3](https://stacks.math.columbia.edu/tag/0AG3)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover

universe u w t

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {M : Type u} {τ : Type t} [AddCommGroup M] [Module S M] [SetLike τ M]
  [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- The global sections of the `n`-th twist `M̃(n) = M̃ ⊗_{𝒪_X} 𝒪_X(n)` of the sheaf associated
to a graded module on `X = Proj S`. -/
public abbrev twistedModuleGlobalSections (n : ℤ) : Type _ :=
  ((((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
      (((AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
    ((associatedModuleSheaf 𝒮 𝒨))).obj ((twistingSheaf 𝒮 n)))).val.obj (op ⊤)

/-- The isomorphism `M(n)~ ≅ M̃(n)` of Tag 01MT is bijective on global sections. -/
public theorem bijective_moduleTwistIso_inv_app_top (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    Function.Bijective (((moduleTwistIso 𝒮 𝒨 hcover n).inv.val.app (op ⊤)).hom) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    ((Functor.mapIso (_root_.SheafOfModules.evaluation _ (op ⊤))
      (moduleTwistIso 𝒮 𝒨 hcover n).symm).isIso_hom)

/-- **Equation 0AG3: the canonical map `M_n ⟶ Γ(X, M̃(n))`.** A homogeneous element of degree
`n` gives a global section of `M(n)~`, which the isomorphism `M(n)~ ≅ M̃(n)` of Tag 01MT turns
into a global section of the twist `M̃(n)`. -/
@[stacks 0AG3]
public def degreeNToTwistedGlobalSections (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    𝒨 n →+ twistedModuleGlobalSections 𝒮 𝒨 n :=
  (((moduleTwistIso 𝒮 𝒨 hcover n).inv.val.app (op ⊤)).hom.toAddMonoidHom).comp
    (degreeNToGlobalSections 𝒮 𝒨 n)

/-- The canonical map `M_n ⟶ Γ(X, M̃(n))` is bijective exactly when the canonical map
`M_n ⟶ Γ(X, M(n)~)` is: the two differ by an isomorphism of sheaves of modules. -/
public theorem bijective_degreeNToTwistedGlobalSections_iff (hcover : DegreeOneCover 𝒮) (n : ℤ) :
    Function.Bijective (degreeNToTwistedGlobalSections 𝒮 𝒨 hcover n) ↔
      Function.Bijective (degreeNToGlobalSections 𝒮 𝒨 n) :=
  (bijective_moduleTwistIso_inv_app_top 𝒮 𝒨 hcover n).of_comp_iff'
    (degreeNToGlobalSections 𝒮 𝒨 n)

end Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover

end
