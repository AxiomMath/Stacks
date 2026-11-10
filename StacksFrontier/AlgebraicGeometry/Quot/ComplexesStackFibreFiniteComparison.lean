module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackTangentSpaceBase
public import StacksFrontier.Deformation.Artin.FiniteDimensional.CoefficientLiftComparison

/-!
# The fibre of `Complexes_{X/Y}` from a comparison with derived lifts (towards Stacks 0DLL)

The third and fourth paragraphs of the proof of Stacks 0DLL compute the tangent space and the
infinitesimal automorphisms of the fibre `𝒲 = Complexes_{X/Y} ×_{𝒮_Y} (Sch/Spec k)` at the point
`w₀` of a field point `x₀`: a lift of `w₀` over `k[V]` is a complex on `X_V` restricting to `E₀`,
which on the small étale site of `X₀` is a lift of `E₀` to `O₀[V] = O₀ ⊕ (O₀ ⊗_k V)` in the
sense of Stacks 0DIZ.

This file specializes the two formal halves of that computation, the theorems
`finiteDimensional_tangentModuleAt_twoFibreProduct_of_coefficientLiftComparison` and
`finiteDimensional_localizedAutomorphismFunctorTangent_twoFibreProduct_of_coefficientHom` of the
namespace `Deformation.Artin`, to `𝒲` and `w₀ = fibreBasePoint D x₀`: the inputs about the second
factor `(Sch/Spec k)` and the base `𝒮_Y` (fibred in groupoids, (RS\*), tangent spaces) are
discharged, so what remains is (RS\*) for `Complexes_{X/Y}`, the comparison with derived lifts, and
the finiteness of `Ext¹(K₀, K₀)` and `Ext⁰(K₀, K₀)`. The results are the hypotheses
`AlgebraicGeometry.Space.ComplexesSituation.FibreTangentFinite` and
`AlgebraicGeometry.Space.ComplexesSituation.FibreInfFinite`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.fibreTangentFinite_of_coefficientLiftComparison`
* `AlgebraicGeometry.Space.ComplexesSituation.fibreInfFinite_of_coefficientHom`

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 07WY](https://stacks.math.columbia.edu/tag/07WY)
-/

/- See `StacksFrontier/Deformation/ToposThickening/CoefficientSquareZeroReduction.lean`: this
instance makes the universe unifier get stuck on sheaves of modules over a site in
`Type (u + 1)`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.Artin Deformation.ComplexLift

namespace AlgebraicGeometry.Space

universe d d₀ u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

attribute [local instance] complexesCategory

/-- The field `k` of a field point `x₀` of `Complexes_{X/Y}` over `Spec k ⟶ S` is an object of
the site. -/
theorem contains_spec_of_point {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    B.Contains (Spec (.of k)) := by
  have hb : B.inclusion.obj ((complexesFunctor D).obj x₀).left = Spec (.of k) :=
    congrArg Comma.left hx₀
  exact hb ▸ ((complexesFunctor D).obj x₀).left.property

/-- The point `w₀` of the fibre `𝒲` lies over `Spec k`, as an object of the site over `S`. -/
theorem fibreBasePoint_eq_algebraOver {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k))) :
    (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
      (baseProj D.Y) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom)).obj (fibreBasePoint D x₀) =
      algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk :=
  BigFppfOver.obj_injective_post_inclusion B S hS (fibreBasePoint_base D iΛ x₀ hx₀)

section Comparison

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O₀ : Sheaf J CommRingCat.{u}}

/-- **The tangent-space hypothesis on the fibre, from a comparison with derived lifts.** Let
`Complexes_{X/Y}` satisfy (RS\*) (Stacks 0DLK, `rsC`) and let `x₀` be a field point over
`Spec k ⟶ Spec Λ ⟶ S`. A coefficient lift comparison `Φ` for the fibre `𝒲` at `w₀` (lifts of
`w₀` over `k[V]` ↦ lifts of `K₀` to `O₀[V]`, Stacks 0DIZ) gives
`AlgebraicGeometry.Space.ComplexesSituation.FibreTangentFinite` as soon as
`Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k k))⟦1⟧) = Ext¹(K₀, K₀)` is finite dimensional. The second factor
`(Sch/Spec k)` and the base `𝒮_Y` satisfy (RS\*), and the tangent spaces of `(Sch/Spec k)` are
finite dimensional by the scheme case of Stacks 07X1. -/
theorem fibreTangentFinite_of_coefficientLiftComparison
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (coefficientRing θ V)))]
    [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
    (K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
    (Φ : CoefficientLiftComparison.{d, d₀} B S hS iΛ hk (complexesFunctor D) (baseProj D.Y)
      (Over.map x₀.T.left.hom) (complexesToBaseObjects D)
      (schemePointToBase D.Y x₀.T.left x₀.T.hom) (fibreBasePoint D x₀)
      (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk) θ K₀)
    [FiniteDimensional k ((coefficientExtLinearFunctor.{d₀} θ K₀.obj).obj (FGModuleCat.of k k))] :
    FibreTangentFinite D iΛ x₀ hx₀ := fun hD =>
  finiteDimensional_tangentModuleAt_twoFibreProduct_of_coefficientLiftComparison hfib
    (baseProj_isFiberedInGroupoids D.Y) (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
    (complexesToBaseObjects_comp D) (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom) rsC
    (baseProj_satisfiesRSStar D.Y) (overMap_satisfiesRSStar x₀.T.left)
    (fibreBasePoint_base D iΛ x₀ hx₀) hfinite hqc
    (fun hz₀ hD' => finiteDimensional_tangentModuleAt_fibreBasePoint_snd D iΛ x₀ hx₀ hfinite
      hqc hz₀ hD') Φ hD

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The infinitesimal-automorphism hypothesis on the fibre, from the groups
`Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))`.** Let `Complexes_{X/Y}` satisfy (RS\*) (Stacks 0DLK, `rsC`) and let
`x₀` be a field point over `Spec k ⟶ Spec Λ ⟶ S`. If the groups `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k V))`
(Stacks 0DIZ (1)) map, naturally in `V` and surjectively at `V = k`, onto the infinitesimal
automorphisms of the trivial deformation of `w₀` over `k[V]` (`aut`, `haut`, `hsurj`; in the proof
of Stacks 0DLL, `φ ↦ 1 + φ` on `z^*E₀`), then
`AlgebraicGeometry.Space.ComplexesSituation.FibreInfFinite` holds as soon as
`Hom(K₀, K₀ ⊗^L O₀) = Ext⁰(K₀, K₀)` is finite dimensional. -/
theorem fibreInfFinite_of_coefficientHom
    (hfib : (complexesFunctor D).IsFiberedInGroupoids)
    (rsC : SatisfiesRSStar B S hS (complexesFunctor D) hfib)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : ComplexesObject D)
    (hx₀ : (complexesFunctor D ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hk : B.Contains (Spec (.of k)))
    (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)
    [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (coefficientRing θ V)))]
    [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
    (K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))
    [FiniteDimensional k ((coefficientHomLinearFunctor.{d₀} θ K₀.obj).obj (FGModuleCat.of k k))]
    (aut : ∀ V : FGModuleCat.{u} k, (coefficientHomLinearFunctor.{d₀} θ K₀.obj).obj V →
      (trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V) ⟶
        trivialDeformation k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))
          ((fgSiteModule B hk).obj V)))
    (haut : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (g : (coefficientHomLinearFunctor.{d₀} θ K₀.obj).obj V),
      aut W ((coefficientHomLinearFunctor.{d₀} θ K₀.obj).map f g) =
        (infinitesimalAutomorphismSetFunctor k B S hS
          (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
          (TwoFibreProductOver.structureFunctor (complexesFunctor D) (Over.map x₀.T.left.hom)
            (baseProj D.Y) (complexesToBaseObjects D) (schemePointToBase D.Y x₀.T.left x₀.T.hom))
          (fibreBasePoint D x₀) (fibreBasePoint_eq_algebraOver D iΛ x₀ hx₀ hk)
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfib
            (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
            (baseProj_isFiberedInGroupoids D.Y) (complexesToBaseObjects_comp D)
            (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom))).map
          ((fgSiteModule B hk).map f) (aut V g))
    (hsurj : Function.Surjective (aut (FGModuleCat.of k k))) :
    FibreInfFinite D iΛ x₀ hx₀ := fun hD y hy P =>
  finiteDimensional_localizedAutomorphismFunctorTangent_twoFibreProduct_of_coefficientHom.{d₀}
    (θ := θ) (K₀ := K₀) hfib
    (baseProj_isFiberedInGroupoids D.Y) (Functor.IsFiberedInGroupoids.over_map x₀.T.left.hom)
    (complexesToBaseObjects_comp D) (schemePointToBase_comp D.Y x₀.T.left x₀.T.hom) rsC
    (baseProj_satisfiesRSStar D.Y) (overMap_satisfiesRSStar x₀.T.left)
    (fibreBasePoint_base D iΛ x₀ hx₀) aut haut hsurj hD y hy P

end Comparison

end ComplexesSituation

end AlgebraicGeometry.Space

end
