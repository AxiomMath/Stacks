module

public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Smoothness

/-!
# The datum extracted from the conclusion of Stacks 07XH in Stacks Example 98.12.8

Let `Λ` be a Noetherian ring, `𝔪 ⊂ Λ` a maximal ideal, `R = Λ_𝔪^∧`, `Λ → C → R` a
factorization with `C` a `Λ`-algebra, `𝒳 = 𝒮_F` the category fibred in sets of Stacks
Example 98.12.8 and `ξ` its formal object over `R`. This file proves the step of the Example
from the conclusion of Stacks Lemma 98.12.7 for `𝒳` and `ξ` to the datum: a finite type
`Λ`-algebra `A` with a maximal ideal `𝔪_A` lying over `𝔪`, `κ(𝔪) = κ(𝔪_A)`, condition (4) of
Stacks 02HT for `Λ → A` at `𝔪_A` (hence `Λ → A` smooth at `𝔪_A`), and a `Λ`-algebra map `C → A`.

## Main results

* `Deformation.Artin.GRingNecessity.exists_lift_smallExtension_of_algebraizationConclusion`: the
  datum with condition (4) of Stacks 02HT, from the conclusion of Stacks 07XH for `𝒳` and `ξ`.
* `Deformation.Artin.GRingNecessity.exists_smooth_of_algebraizationConclusion`: the datum with
  smoothness at `𝔪_A`.

## Implementation notes

The last clause of the conclusion identifies the completion of the local ring of `U` at `u₀`
with the base `R'` of an object `x_R` whose formal object is isomorphic to `ξ`, compatibly with
the morphisms to `U`; this gives a morphism `Spec R' → U` over `S` sending the closed point to
`u₀`. The isomorphism of formal objects induces a morphism `Spec R → Spec R'` over `S`
preserving closed points, and `R ≅ Λ_𝔪^∧` over `Λ`. Following the closed point and the residue
fields through `Spec R → Spec R' → U → S` shows that `u₀` lies over `𝔪` and that `Λ → κ(u₀)` is
surjective; the residue field isomorphism of the conclusion is not needed for this. An affine open
neighbourhood `V` of `u₀` inside the preimage of `Spec C` under the factorization `U → S'` given by
the object over `U` provides `A = Γ(U, V)` with `C → A`, and `𝔪_A` is the kernel of
`A → κ(u₀)`. Condition (4) of Stacks 02HT at `𝔪_A` is `lift_smallExtension_of_isVersalAt`, and
smoothness at `𝔪_A` follows by Stacks 02HT (`Algebra.isSmoothAt_tfae`), as in the source.

The statements assume `C` of finite type over `Λ`, as the source does, although the extraction
does not use it.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingNecessity

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/-! ### The morphism `Spec R' → U` of the last clause of the conclusion -/

/-- A local map from a local ring of `X` to a local ring sends the closed point of its spectrum to
the point of `X`. -/
theorem specMap_fromSpecStalk_closedPoint {X : Scheme.{u}} (x : X) {R : Type u} [CommRing R]
    [IsLocalRing R] (ψ : X.presheaf.stalk x →+* R) [IsLocalHom ψ] :
    (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x) (specClosedPoint R) = x :=
  (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := CommRingCat.ofHom ψ))).trans
      Scheme.fromSpecStalk_closedPoint)

/-- The morphism `Spec R → X` given by an isomorphism of the completion of `𝒪_{X,x}` with a
local ring `R` sends the closed point to `x`. -/
theorem completedLocalRing_specMap_closedPoint {X : Scheme.{u}} (x : X) {R : Type u}
    [CommRing R] [IsLocalRing R] (eR : Scheme.completedLocalRing X x ≃+* R) :
    (Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) (Scheme.completedLocalRing X x))) ≫
      X.fromSpecStalk x) (specClosedPoint R) = x := by
  have : IsLocalHom eR.toRingHom := ⟨fun a ha => eR.symm_apply_apply a ▸ ha.map eR.symm⟩
  have := isLocalHom_algebraMap_adicCompletion (X.presheaf.stalk x)
  have h := specMap_fromSpecStalk_closedPoint x (eR.toRingHom.comp
    (algebraMap (X.presheaf.stalk x) (Scheme.completedLocalRing X x)))
  rwa [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at h

section Point

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]

/-- A point `u₀` of a scheme over `S` which is the image of the closed point of a complete local
base whose closed point lies over `𝔪` with residue field a quotient of `Λ`, by a morphism over
`S`, lies over `𝔪` and has residue field a quotient of `Λ`. -/
theorem closedPoint_of_specMap {X : Scheme.{u}} (fX : X ⟶ Spec (.of Λ)) (u₀ : X)
    {A : FormalBase (Spec (.of Λ))} (ρ : Spec (.of A.R) ⟶ X)
    (hρc : ρ (specClosedPoint A.R) = u₀) (hρS : ρ ≫ fX = A.toS)
    (hA : A.toS (specClosedPoint A.R) = closedPointOf 𝔪)
    (hsA : Function.Surjective (residueAlgebraMap A.toS (specClosedPoint A.R))) :
    fX u₀ = closedPointOf 𝔪 ∧ Function.Surjective (residueAlgebraMap fX u₀) := by
  refine ⟨(congrArg fX hρc).symm.trans ((Scheme.Hom.comp_apply ρ fX _).symm.trans
    ((congrArg (fun ψ => ψ (specClosedPoint A.R)) hρS).trans hA)), ?_⟩
  have h := residueAlgebraMap_surjective_of_comp ρ fX (specClosedPoint A.R) (hρS ▸ hsA)
  exact hρc ▸ h

end Point

/-! ### The closed point of the base of the object realizing `ξ` -/

section Base

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]
  (C : Type u) [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] Completion 𝔪) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of Λ)))

/-- A formal object of `𝒳` receiving a morphism from `ξ` has its closed point over `𝔪` and its
residue field there a quotient of `Λ`. -/
theorem closedPoint_of_hom_formalObject
    {Y : FormalObject B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p}
    (h : formalObject 𝔪 C φ B hS ⟶ Y) :
    Y.base.toS (specClosedPoint Y.base.R) = closedPointOf 𝔪 ∧
      Function.Surjective (residueAlgebraMap Y.base.toS (specClosedPoint Y.base.R)) := by
  have hξ := isCompletionBase_formalObject 𝔪 C φ B hS
  exact closedPoint_of_specMap 𝔪 Y.base.toS _ (FormalObject.Hom.baseMap h) (baseMap_closedPoint h)
    (FormalObject.Hom.baseMap_spec h).1 (toS_closedPoint_of_isCompletionBase hξ)
    (residueAlgebraMap_surjective_of_isCompletionBase hξ)

/-- The complete local base of an object of `𝒳` whose formal object receives a morphism from `ξ`
has its closed point over `𝔪` and its residue field there a quotient of `Λ`. -/
theorem chosenBase_closedPoint
    (xR : CompleteLocalObjects B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p)
    (e : formalObject 𝔪 C φ B hS ⟶ (approximationFunctor B (Spec (.of Λ)) hS
      (factorizationCategory 𝔪 C B hS).val.p (factorizationCategory 𝔪 C B hS).property).obj xR) :
    (chosenBase B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p xR.obj).toS
        (specClosedPoint (chosenBase B (Spec (.of Λ)) hS
          (factorizationCategory 𝔪 C B hS).val.p xR.obj).R) = closedPointOf 𝔪 ∧
      Function.Surjective (residueAlgebraMap
        (chosenBase B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p xR.obj).toS
        (specClosedPoint (chosenBase B (Spec (.of Λ)) hS
          (factorizationCategory 𝔪 C B hS).val.p xR.obj).R)) := by
  obtain ⟨-, hbase, -⟩ := (approximationFunctorData B (Spec (.of Λ)) hS
    (factorizationCategory 𝔪 C B hS).val.p (factorizationCategory 𝔪 C B hS).property).2
  exact hbase xR ▸ closedPoint_of_hom_formalObject 𝔪 C φ B hS e

/-- **Stacks Example 98.12.8, from the conclusion of Stacks 07XH to the datum.** Let `C` be a
finite type `Λ`-algebra (as in the source; the proof does not use this) and `φ : C → Λ_𝔪^∧` a
`Λ`-algebra map. If the conclusion of Stacks Lemma 98.12.7 holds for the category `𝒳 = 𝒮_F` and
the formal object `ξ` of the Example, then there are a finite type `Λ`-algebra `A` and a maximal
ideal `𝔪_A` of `A` lying over `𝔪`, with `κ(𝔪) → κ(𝔪_A)` bijective and `Λ → A`, `𝔪_A` satisfying
condition (4) of Stacks 02HT (the last condition of `Algebra.isSmoothAt_tfae`), together with a
`Λ`-algebra map `C → A`. -/
@[stacks 07XI "the datum read off the conclusion of 07XH: `A` of finite type, `𝔪_A` over `𝔪` \
with `κ(𝔪) = κ(𝔪_A)`, condition (4) of 02HT for `Λ → A` at `𝔪_A`, and `C → A`"]
theorem exists_lift_smallExtension_of_algebraizationConclusion [Algebra.FiniteType Λ C]
    (h : AlgebraizationConclusion B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS)
      (formalObject 𝔪 C φ B hS)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra Λ A), Algebra.FiniteType Λ A ∧
      ∃ (mA : Ideal A) (_ : mA.IsMaximal) (hmA : 𝔪 = mA.comap (algebraMap Λ A)),
        Function.Bijective (Ideal.ResidueField.map 𝔪 mA (algebraMap Λ A) hmA) ∧
        (∀ (T₂ T₁ : Type u) [CommRing T₂] [CommRing T₁] [IsLocalRing T₂] [IsLocalRing T₁]
          [IsArtinianRing T₂] [IsArtinianRing T₁] [Algebra Λ T₂] [Algebra Λ T₁]
          (e : T₂ →ₐ[Λ] T₁), Function.Surjective e →
          IsSimpleModule T₂ (RingHom.ker (e : T₂ →+* T₁)) →
          ∀ (g : A →ₐ[Λ] T₁) (hq : (maximalIdeal T₁).comap (g : A →+* T₁) = mA),
            Function.Surjective (Ideal.ResidueField.mapₐ mA (maximalIdeal T₁) g hq.symm) →
            ∃ g' : A →ₐ[Λ] T₂, e.comp g' = g) ∧
        Nonempty (C →ₐ[Λ] A) := by
  obtain ⟨U, u₀, V₀, -, x, hx, hlft, -, -, -, hvers, xR, e, r, eR, -, hρ⟩ := h
  subst hx
  -- `u₀` lies over `𝔪`, with residue field a quotient of `Λ`
  obtain ⟨hcp, hsurjR⟩ := chosenBase_closedPoint 𝔪 C φ B hS xR e.hom
  have hρS := (congrArg (· ≫ (objScheme 𝔪 C B hS x.1).hom)
    ((Category.comp_id _).symm.trans hρ).symm).trans
    (structureHom_comp B hS (eqToHom (chosenBase_eq B (Spec (.of Λ)) hS
      (factorizationCategory 𝔪 C B hS).val.p xR.obj).symm ≫
      (factorizationCategory 𝔪 C B hS).val.p.map r))
  obtain ⟨hu₀, hsurjU⟩ := closedPoint_of_specMap 𝔪 (objScheme 𝔪 C B hS x.1).hom u₀ _
    (completedLocalRing_specMap_closedPoint u₀ eR) hρS hcp hsurjR
  have hkerU : RingHom.ker (residueAlgebraMap (objScheme 𝔪 C B hS x.1).hom u₀) = 𝔪 :=
    (ker_residueAlgebraMap _ u₀).trans (congrArg PrimeSpectrum.asIdeal hu₀)
  -- an affine chart `Spec A ∋ u₀` mapping to `Spec C`
  obtain ⟨g, hg⟩ := factors_of_obj x.1
  obtain ⟨W, hW, hu₀W, gC, hgC⟩ :=
    exists_affineOpen_chart 𝔪 C (objScheme 𝔪 C B hS x.1).hom g hg u₀ hu₀
  let := chartAlgebra (objScheme 𝔪 C B hS x.1).hom hW
  have hψ₀ := chartResidue_comp_algebraMap (objScheme 𝔪 C B hS x.1).hom hW hu₀W
  have hsurj : Function.Surjective ((chartResidue hW hu₀W).comp
      (algebraMap Λ Γ((objScheme 𝔪 C B hS x.1).left, W))) := hψ₀ ▸ hsurjU
  have hker : RingHom.ker ((chartResidue hW hu₀W).comp
      (algebraMap Λ Γ((objScheme 𝔪 C B hS x.1).left, W))) = 𝔪 := hψ₀ ▸ hkerU
  have hmax := ker_isMaximal_of_surjective_comp (chartResidue hW hu₀W) hsurj
  have : LocallyOfFiniteType (objScheme 𝔪 C B hS x.1).hom := hlft
  exact ⟨Γ((objScheme 𝔪 C B hS x.1).left, W), inferInstance, inferInstance,
    finiteType_chartAlgebra (objScheme 𝔪 C B hS x.1).hom hW, RingHom.ker (chartResidue hW hu₀W),
    hmax, eq_comap_ker 𝔪 _ hker, residueField_map_bijective_of_surjective_comp 𝔪 _ hsurj hker,
    lift_smallExtension_of_isVersalAt 𝔪 C φ B hS x.1 u₀ hvers hsurjU hkerU hW hu₀W,
    ⟨chartAlgHom C (objScheme 𝔪 C B hS x.1).hom hW gC hgC⟩⟩

/-- **Stacks Example 98.12.8, the datum with smoothness.** Let `C` be a finite type `Λ`-algebra
and `φ : C → Λ_𝔪^∧` a `Λ`-algebra map. If the conclusion of Stacks Lemma 98.12.7 holds for the
category `𝒳 = 𝒮_F` and the formal object `ξ` of the Example, then there are a finite type
`Λ`-algebra `A` and a maximal ideal `𝔪_A` of `A` lying over `𝔪`, with `κ(𝔪) → κ(𝔪_A)` bijective
and `Λ → A` smooth at `𝔪_A` (by condition (4) and Stacks 02HT), together with a `Λ`-algebra map
`C → A`. -/
theorem exists_smooth_of_algebraizationConclusion [Algebra.FiniteType Λ C]
    (h : AlgebraizationConclusion B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS)
      (formalObject 𝔪 C φ B hS)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra Λ A), Algebra.FiniteType Λ A ∧
      ∃ (mA : Ideal A) (_ : mA.IsMaximal) (hmA : 𝔪 = mA.comap (algebraMap Λ A)),
        Function.Bijective (Ideal.ResidueField.map 𝔪 mA (algebraMap Λ A) hmA) ∧
        Algebra.IsSmoothAt Λ mA ∧ Nonempty (C →ₐ[Λ] A) := by
  obtain ⟨A, _, _, hA, mA, hmax, hmA, hbij, hlift, hCA⟩ :=
    exists_lift_smallExtension_of_algebraizationConclusion 𝔪 C φ B hS h
  exact ⟨A, _, _, hA, mA, hmax, hmA, hbij, ((Algebra.isSmoothAt_tfae mA).out 4 1).mp hlift, hCA⟩

end Base

end Deformation.Artin.GRingNecessity

end
