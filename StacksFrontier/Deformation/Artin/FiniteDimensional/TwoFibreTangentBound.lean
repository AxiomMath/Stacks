module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger
public import StacksFrontier.Deformation.Artin.FiniteDimensional.NaturalLinearBound
public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreSideMaps

/-!
# The tangent space of a 2-fibre product from its second factor and a fibre invariant

Let `F : 𝒳 ⥤ 𝒴` and `G : 𝒵 ⥤ 𝒴` be `1`-morphisms of categories fibred in groupoids over the big
fppf site of `S` satisfying (RS*), and let `w₀` be an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over a field `k`
of finite type over `S`.  A lift of `w₀` over `k[M]` has an image in `𝒵`, a lift of the second
component `z₀` of `w₀`; what is left of it lives "in the fibre" over that image.

This file bounds the tangent space of Stacks 07WY of `𝒲` at `w₀` by that of `𝒵` at `z₀` and
any invariant of the lifts which, together with their images in `𝒵`, separates them: if the
lifts of `w₀` over `k[M]` carry a class in a `k`-linear functor `G₂(M)`, natural in `M`, and
two lifts over `k[ε]` with the same image in `𝒵` and the same class are isomorphic, then
`T𝓕_{𝒲,k,w₀}` is finite dimensional as soon as `T𝓕_{𝒵,k,z₀}` and `G₂(k)` are.

In the proof of Stacks 0DLL, `𝒵 = Spec k`, whose tangent space is `Der_Λ(k, k)` and finite
dimensional by Stacks 07X1, and the class of a lift `(z, E)` is `E` read against the trivial lift
`z^*E₀`, in `Ext¹(E₀, E₀ ⊗ M)`.

## Main results

* `Deformation.Artin.finiteDimensional_tangentModuleAt_twoFibreProduct_of_fibre`

## References

* [Stacks Project, Tag 07WY](https://stacks.math.columbia.edu/tag/07WY)
* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 0CXQ](https://stacks.math.columbia.edu/tag/0CXQ)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u u₁ v₁ u₂ v₂ u₃ v₃ v₄

@[expose] public noncomputable section

namespace Deformation.Artin

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (hk : B.Contains (Spec (.of k)))
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (p𝒵 : 𝒵 ⥤ BigFppfOver B S hS)
  (F : 𝒳 ⥤ 𝒴) (G : 𝒵 ⥤ 𝒴)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (h𝒵 : p𝒵.IsFiberedInGroupoids)
  (w₀ : TwoFibreProductOver p𝒳 p𝒵 p𝒴 F G)
  (hw : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G).obj w₀ =
    algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk)

include hw in
/-- The second component of `w₀` lies over `Spec k`. -/
theorem snd_obj_eq_algebraOver :
    p𝒵.obj ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀) =
      algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk :=
  (Functor.congr_obj
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒵) (p𝒮 := p𝒴) (F := F) (G := G))
    w₀).trans hw

/-- **The map from the lifts of `w₀` to the lifts of its second component.**  The class of a
lift of `w₀` over `k[M]` is sent to the class of its image under the second projection
`𝒲 ⥤ 𝒵` (Stacks 07YA). -/
abbrev sndLiftClass (M : SiteModule k B) :
    squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw M →
      squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        p𝒵 ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀)
        (snd_obj_eq_algebraOver B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw) M :=
  liftClassOfOneMorphismTransport k B S hS _ hk _ p𝒵 (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G)
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒵) (p𝒮 := p𝒴) (F := F) (G := G)) w₀ hw _
    (snd_obj_eq_algebraOver B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw) (Iso.refl _)
    (CategoryTheory.IsHomLift.id (snd_obj_eq_algebraOver B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw)) M

/-- **Stacks 07WY for a 2-fibre product, from the second factor and a fibre invariant.**  Let
`F : 𝒳 ⥤ 𝒴` and `G : 𝒵 ⥤ 𝒴` be `1`-morphisms of categories fibred in groupoids satisfying
(RS*), `k` a field presented through `Spec k ⟶ Spec Λ ⟶ S` with the composite locally of finite
type and quasi-compact, and `w₀` an object of `𝒲 = 𝒳 ×_𝒴 𝒵` over `Spec k`, with second
component `z₀`.  Suppose that

* the tangent space of `𝓕_{𝒵,k,z₀}` is finite dimensional, and
* the lifts of `w₀` over `k[M]` carry a class `θ` in a `k`-linear functor `G₂(M)` with `G₂(k)`
  finite dimensional, compatibly with pullback of lifts along every linear map, such that two
  lifts over `k[ε]` with the same image in `𝒵` and the same class are isomorphic.

Then the tangent space of `𝓕_{𝒲,k,w₀}` is finite dimensional, for every witness that it is a
deformation category.  (RS*) for `𝒲` is Stacks 0CXQ. -/
theorem finiteDimensional_tangentModuleAt_twoFibreProduct_of_fibre
    (hF : F ⋙ p𝒴 = p𝒳) (hG : G ⋙ p𝒴 = p𝒵)
    (rs𝒳 : SatisfiesRSStar B S hS p𝒳 h𝒳) (rs𝒴 : SatisfiesRSStar B S hS p𝒴 h𝒴)
    (rs𝒵 : SatisfiesRSStar B S hS p𝒵 h𝒵)
    (hw₀ : (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT𝒵 : ∀ (hz₀ : (p𝒵 ⋙ Over.post B.inclusion).obj
        ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
        (p𝒵 ⋙ Over.post B.inclusion) ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀)
        hz₀).projection),
      FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (predeformationCategory iΛ (p𝒵 ⋙ Over.post B.inclusion)
          ((TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀) hz₀).projection) hD
        (FGModuleCat.of k k)))
    (G₂ : FGModuleCat.{u} k ⥤ ModuleCat.{v₄} k) [G₂.Additive] [G₂.Linear k]
    [FiniteDimensional k (G₂.obj (FGModuleCat.of k k))]
    (θ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).obj V) → G₂.obj V)
    (hθ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
        hk (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).map f) a b →
        θ W b = G₂.map f (θ V a))
    (hsep : ∀ a b : squareZeroLiftClasses k B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).obj (FGModuleCat.of k k)),
      sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ a =
          sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ b →
        θ (FGModuleCat.of k k) a = θ (FGModuleCat.of k k) b → a = b)
    (hD : IsDeformationCategory.{u, u, u} (predeformationCategory iΛ
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
      hw₀).projection) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (predeformationCategory iΛ
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G ⋙ Over.post B.inclusion) w₀
        hw₀).projection) hD (FGModuleCat.of k k)) := by
  let toS := Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  let z₀ := (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G).obj w₀
  have hz : p𝒵.obj z₀ = algebraOver k B S hS toS hk :=
    snd_obj_eq_algebraOver B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw
  have hz₀ : (p𝒵 ⋙ Over.post B.inclusion).obj z₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    (Functor.congr_obj
      (congrArg (· ⋙ Over.post B.inclusion)
        (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒵) (p𝒮 := p𝒴) (F := F) (G := G)))
      w₀).trans hw₀
  -- The tangent functor of `𝒵` at `z₀`, finite dimensional at `k` by the hypothesis on `𝒵`.
  let TZ := tangentFunctor k B S hS toS hk p𝒵 z₀ hz h𝒵 rs𝒵
  have hDZ := isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS p𝒵 h𝒵
    rs𝒵 iΛ z₀ hz₀ hfinite hqc
  have hTZ : FiniteDimensional k (TZ.functor.obj ((fgSiteModule B hk).obj
      (FGModuleCat.of k k))) := by
    let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor (predeformationCategory iΛ
        (p𝒵 ⋙ Over.post B.inclusion) z₀ hz₀).projection).p) := ⟨hDZ.predeformation⟩
    let : Fact (SchlessingerConditionS2 (Functor.Elements.π
        (isomorphismClasses (BasedCategory.ofFunctor (predeformationCategory iΛ
          (p𝒵 ⋙ Over.post B.inclusion) z₀ hz₀).projection)
          hDZ.predeformation.cofibered))) := ⟨tangentConditionS2 hDZ⟩
    obtain ⟨e, -⟩ := tangentSpace_deformationCategory_linearEquiv_of_tangentFunctorData B S hS iΛ
      toS hk p𝒵 h𝒵 z₀ hz₀ hz TZ hDZ
    have := (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt
      (𝓕 := BasedCategory.ofFunctor (predeformationCategory iΛ
        (p𝒵 ⋙ Over.post B.inclusion) z₀ hz₀).projection) hDZ).mpr (hT𝒵 hz₀ hDZ)
    exact e.finiteDimensional
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  let G₁ := fgSiteModule B hk ⋙ TZ.functor
  have : FiniteDimensional k (G₁.obj (FGModuleCat.of k k)) := hTZ
  let θ₁ : ∀ V : FGModuleCat.{u} k,
      squareZeroLiftClasses k B S hS toS hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).obj V) → G₁.obj V := fun V a =>
    (TZ.liftEquiv _).symm (sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ a)
  have hθ₁ : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W)
      (a : squareZeroLiftClasses k B S hS toS hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw ((fgSiteModule B hk).obj V))
      (b : squareZeroLiftClasses k B S hS toS hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw ((fgSiteModule B hk).obj W)),
      IsPullbackOfSquareZeroLift k B S hS toS hk
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀ hw
        ((fgSiteModule B hk).map f) a b →
        θ₁ W b = G₁.map f (θ₁ V a) := by
    intro V W f a b hab
    apply (TZ.liftEquiv _).injective
    simp only [θ₁, Equiv.apply_symm_apply]
    have h2 := isPullbackOfSquareZeroLift_mapTransport k B S hS toS hk _ p𝒵
      (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 F G)
      (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒵) (p𝒮 := p𝒴) (F := F) (G := G))
      w₀ hw z₀ hz (Iso.refl _) (CategoryTheory.IsHomLift.id hz) h𝒵 _ a b hab
    have h3 := TZ.liftEquiv_natural ((fgSiteModule B hk).map f)
      ((TZ.liftEquiv _).symm (sndLiftClass B S hS iΛ hk p𝒳 p𝒴 p𝒵 F G w₀ hw _ a))
    rw [Equiv.apply_symm_apply] at h3
    exact isPullbackOfSquareZeroLift_unique k B S hS toS hk p𝒵 z₀ hz h𝒵 _ h2 h3
  have hinj : Function.Injective fun a =>
      (θ₁ (FGModuleCat.of k k) a, θ (FGModuleCat.of k k) a) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact hsep a b ((TZ.liftEquiv _).symm.injective hab.1) hab.2
  exact finiteDimensional_tangentModuleAt_of_natural_injective_prod B S hS hk
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 F G) w₀
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒵 p𝒴 F G h𝒳 h𝒵 h𝒴 hF hG) iΛ
    (twoFibreProductOver_satisfiesRSStar B S hS p𝒳 p𝒴 p𝒵 F G h𝒳 h𝒴 h𝒵 hF hG rs𝒳 rs𝒴 rs𝒵)
    hw₀ hw G₁ G₂ θ₁ θ hθ₁ hθ hinj hD

end Deformation.Artin

end
