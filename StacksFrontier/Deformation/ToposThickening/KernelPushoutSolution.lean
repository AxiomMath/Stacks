module

public import StacksFrontier.Deformation.ToposThickening.KernelPushoutAlgebraExtension

/-!
# Solutions of an extension problem over a change of ideal module

Let `S` be a square-zero extension problem of ringed topoi — the problem (91.13.0.1) of
[Stacks Project, Tag 08UF] — with prescribed module `ℱ`, and `φ : ℱ ⟶ 𝒢`. The proof of
[Stacks Project, Tag 0D3Q] shows that every solution `𝒪''` of the problem with ideal module `𝒢`
is the pushout along `φ` of a solution `𝒪'` of `S`. This file records the form of that statement
the body of the proof of [Stacks Project, Tag 0D3X] uses: a solution `𝒪'` of `S` together with a
morphism `𝒪' ⟶ 𝒪''` over the change of ideal module along `φ`. It needs only that pushout `F` of
all extensions of algebras along `φ` is essentially surjective and that post-composition with `φ`
is injective on maps out of the base ideal — no pushout functor of solutions is involved.

## Main results

* `RingedToposExtensionProblem.exists_kernelChangeHom_of_isPushoutFunctor`: every solution
  with ideal module `𝒢` receives a morphism over the change of ideal module along `φ` from a
  solution of `S`.

## References

* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open CompatibleFirstOrderThickening AlgebraExtension

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  (S : RingedToposExtensionProblem X B)
  {A : Sheaf X.J CommRingCat.{w}} {a : A ⟶ X.O}
  (θ : A ≅ (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
  (hθ : θ.hom ≫ (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
      S.f.fSharpInverseImage = a)
  {N : SheafOfModules.{w}
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)} (φ : S.G ⟶ N)

include hθ in
/-- **Every solution over the changed ideal module receives a solution of `S`** (the essential
surjectivity in the proof of [Stacks Project, Tag 0D3Q]). Let `F` be pushout along `φ : ℱ ⟶ 𝒢` of
extensions of `𝒜`-algebras, `𝒜 ≅ f⁻¹𝒪_{B'}`, essentially surjective, and suppose
post-composition with `φ` is injective on maps `f⁻¹𝒥 ⟶ ℱ`. Then every solution `𝒪''` of the
problem with ideal module `𝒢` receives a morphism over the change of ideal module along `φ` from
some solution `𝒪'` of `S`: the extension `F⁻¹(𝒪'')` induces `c` on the base ideal, since its
pushout induces `φ ∘ c`. -/
theorem exists_kernelChangeHom_of_isPushoutFunctor
    [Presheaf.IsLocallySurjective X.J S.baseReductionInverseImagePresheafHom]
    {F : AlgebraExtension a S.G ⥤ AlgebraExtension a N} (hF : IsPushoutFunctor φ F) [F.EssSurj]
    (hinj : ∀ d₁ d₂ : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
        (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj S.G,
      d₁ ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map φ =
        d₂ ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map φ →
        d₁ = d₂)
    (R : (changeKernel S φ).CompatibleFirstOrderThickening) :
    ∃ P : S.CompatibleFirstOrderThickening, Nonempty (KernelChangeHom φ P R) := by
  let ιG := (changeKernel S φ).toAlgebraExtensionFunctor θ hθ
  let P₀ := F.objPreimage (ιG.obj R)
  let h : MapAlong φ P₀ (ιG.obj R) :=
    MapAlong.comp (hF.ι P₀) (F.objObjPreimageIso (ιG.obj R)).hom (Category.comp_id φ)
  have hc : S.idealMap θ hθ P₀ = S.c := by
    refine hinj _ _ ((S.idealMap_comp θ hθ h).trans ?_)
    exact ((changeKernel S φ).idealMap_eq_iff θ hθ _ _).2
      ((changeKernel S φ).isCompatible_toAlgebraExtension θ hθ R)
  have hP₀ : S.IsCompatible θ S.c P₀ := (S.idealMap_eq_iff θ hθ P₀ S.c).1 hc
  exact ⟨S.ofAlgebraExtension θ hθ P₀ hP₀, ⟨S.ofMapAlong θ hθ φ
    (MapAlong.comp (S.toAlgebraExtensionOfAlgebraExtensionIso θ hθ P₀ hP₀).hom h
      (Category.id_comp φ))⟩⟩

end Deformation.ToposThickening.RingedToposExtensionProblem

end
