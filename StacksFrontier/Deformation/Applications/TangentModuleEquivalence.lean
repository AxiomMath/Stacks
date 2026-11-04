module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact

/-!
# The tangent module under a based functor that is an equivalence on fibres

`Deformation.tangentMapAt` is the `k`-linear map on tangent modules induced by a `1`-morphism of
deformation categories. This file records when it is an isomorphism: it is enough that the
comparison on the fibre over the square-zero extension `k[M]` be full, faithful and essentially
surjective. Injectivity is then that a fully faithful functor reflects isomorphy, two objects of
a fibre having the same tangent class exactly when they are isomorphic in that fibre
(`Deformation.tangentClassAt_eq_iff`); surjectivity is essential surjectivity on the fibre,
every tangent class being the class of an object of the fibre
(`Deformation.tangentClassAt_surjective`).

The three conditions are hypotheses on the fibre, not consequences of the based functor being an
equivalence: `Functor.Fiber p A` is cut out by the *equality* `p.obj x = A`, so an equivalence
over the base carries an object of one fibre only to an object lying over a base object
*isomorphic* to `A`. Fullness and faithfulness on fibres do follow from fullness and
faithfulness of the comparison; essential surjectivity does not.

## Main definitions

* `Deformation.tangentLinearEquivOfFiberEquivalence`: the resulting `k`-linear isomorphism of
  tangent modules.

## Main results

* `Deformation.bijective_tangentMapAt_of_fiberEquivalence`: the induced map on tangent modules
  is bijective.
* `Deformation.finiteDimensional_tangentModuleAt_of_fiberEquivalence`: finite-dimensionality of
  the tangent module transports.
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
  {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}

/-- **The map on tangent modules induced by a based functor that is an equivalence on the fibre
over `k[M]` is bijective.** Both halves are the description of the tangent module by classes of
objects of that fibre: a fully faithful comparison reflects isomorphy, which gives injectivity,
and an essentially surjective one hits every class, which gives surjectivity. -/
public theorem bijective_tangentMapAt_of_fiberEquivalence
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p)
    (φ : 𝓕 ⥤ᵇ 𝓖) (M : FGModuleCat.{max v w} k)
    (hfull : (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).Full)
    (hfaithful :
      (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).Faithful)
    (hess : (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).EssSurj) :
    Function.Bijective (tangentMapAt.{u, v, w} h𝓕 h𝓖 φ M) := by
  constructor
  · intro s t hst
    obtain ⟨x, rfl⟩ := tangentClassAt_surjective.{u, v, w} 𝓕 h𝓕 M s
    obtain ⟨y, rfl⟩ := tangentClassAt_surjective.{u, v, w} 𝓕 h𝓕 M t
    rw [tangentMapAt_tangentClassAt.{u, v, w}, tangentMapAt_tangentClassAt.{u, v, w}] at hst
    obtain ⟨e⟩ := (tangentClassAt_eq_iff.{u, v, w} 𝓖 h𝓖 M _ _).mp hst
    exact (tangentClassAt_eq_iff.{u, v, w} 𝓕 h𝓕 M x y).mpr
      ⟨(Functor.FullyFaithful.ofFullyFaithful (fiberFunctor φ
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))).preimageIso e⟩
  · intro t
    obtain ⟨z, rfl⟩ := tangentClassAt_surjective.{u, v, w} 𝓖 h𝓖 M t
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) z
    refine ⟨tangentClassAt.{u, v, w} 𝓕 h𝓕 M x, ?_⟩
    rw [tangentMapAt_tangentClassAt.{u, v, w}]
    exact (tangentClassAt_eq_iff.{u, v, w} 𝓖 h𝓖 M _ _).mpr ⟨e⟩

/-- **The `k`-linear isomorphism of tangent modules** induced by a based functor that is an
equivalence on the fibre over `k[M]`. -/
public noncomputable def tangentLinearEquivOfFiberEquivalence
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p)
    (φ : 𝓕 ⥤ᵇ 𝓖) (M : FGModuleCat.{max v w} k)
    (hfull : (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).Full)
    (hfaithful :
      (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).Faithful)
    (hess : (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).EssSurj) :
    ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M) ≃ₗ[k] ↥(tangentModuleAt.{u, v, w} 𝓖 h𝓖 M) :=
  LinearEquiv.ofBijective (tangentMapAt.{u, v, w} h𝓕 h𝓖 φ M)
    (bijective_tangentMapAt_of_fiberEquivalence.{u, v, w} h𝓕 h𝓖 φ M hfull hfaithful hess)

/-- **Finite-dimensionality of the tangent module transports** along a based functor that is an
equivalence on the fibre over `k[M]`. -/
public theorem finiteDimensional_tangentModuleAt_of_fiberEquivalence
    (h𝓕 : IsDeformationCategory.{u, v, w} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, v, w} 𝓖.p)
    (φ : 𝓕 ⥤ᵇ 𝓖) (M : FGModuleCat.{max v w} k)
    (hfull : (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).Full)
    (hfaithful :
      (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).Faithful)
    (hess : (fiberFunctor φ ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).EssSurj)
    (hfin : FiniteDimensional k ↥(tangentModuleAt.{u, v, w} 𝓖 h𝓖 M)) :
    FiniteDimensional k ↥(tangentModuleAt.{u, v, w} 𝓕 h𝓕 M) :=
  (tangentLinearEquivOfFiberEquivalence.{u, v, w} h𝓕 h𝓖 φ M hfull hfaithful
    hess).symm.finiteDimensional

end

end Deformation

end
