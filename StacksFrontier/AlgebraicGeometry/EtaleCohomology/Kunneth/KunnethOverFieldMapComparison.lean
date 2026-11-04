module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.KunnethOverSeparablyClosedField
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoOfIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KunnethMapThroughProjectionFormula

/-!
# The Künneth map of Stacks 0F1P is the Künneth map of Stacks 0F1E

On the derived categories `D(-_étale, Λ)` of `Stacks.EtaleCohomology.EtaleCoefficients`, the
proof of [Stacks, Tag 0F1P] builds the map

`Rf_*E ⊗^L Rg_*K ⟶ Rf_*(E ⊗^L f⁻¹Rg_*K) ⟶ Rf_*Rp_*(p⁻¹E ⊗^L q⁻¹K) ≅ R(p ≫ f)_*(p⁻¹E ⊗^L q⁻¹K)`

(`Stacks.EtaleCohomology.EtaleCoefficients.kunnethMapOfBaseChange`), while [Stacks, Tag 0F1E]
defines the Künneth map `Stacks.EtaleCohomology.EtaleCoefficients.kunnethMap` directly. This file
proves that the two agree, for every commutative square of schemes.

The input is the composition law of the comparison `c⁻¹(M ⊗^L N) ≅ c⁻¹M ⊗^L c⁻¹N` of
[Stacks, Tag 07A4] along the composite inverse image `f⁻¹ ⋙ p⁻¹ ≅ (p ≫ f)⁻¹` of
`Stacks.EtaleCohomology.EtaleCoefficients.pullbackCompIso`. That isomorphism is the composition
isomorphism of [Stacks, Tag 0D6D] for the composite morphism of ringed topoi, followed by the
isomorphism of derived pullbacks along isomorphic morphisms of ringed topoi, so its composition law
is the one of [Stacks, Tag 07A4] along Tag 0D6D (`derivedPullbackTensorIso_hom_app_comp`) followed
by the compatibility of 07A4 with isomorphic morphisms
(`derivedPullbackIsoOfIso_hom_app_comp_derivedPullbackTensorIso_hom_app`), both in the namespace
`Stacks.Sheaves.DerivedPullback`.

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `pullbackCompIso_hom_app_comp_pullbackTensorIso_hom_app` — **the composition law of
  `pullbackTensorIso` (Stacks 07A4) along `pullbackCompIso`**, for any composable `p`, `f`.
* `kunnethMapOfBaseChange_eq_kunnethMap` — the map of the proof of Tag 0F1P is the Künneth map of
  Tag 0F1E, for every commutative square.
* `kunnethOverFieldMap_eq_kunnethMap` — in particular for the fibre square of two schemes over a
  field.

## References

* [Stacks Project, Tag 0F1P](https://stacks.math.columbia.edu/tag/0F1P)
* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]


/-- The rearrangement behind `pullbackCompIso_hom_app_comp_pullbackTensorIso_hom_app`, stated on
variables. -/
private theorem comp_tensor_algebra {D : Type*} [Category D]
    {T : D × D ⥤ D} {P₀ P₁ P₂ Q₀ : D} {A₁ B₁ A₂ B₂ A₃ B₃ : D}
    {a : P₀ ⟶ P₁} {i : P₁ ⟶ P₂} {μψ : P₂ ⟶ T.obj (A₃, B₃)} {μφ : P₁ ⟶ T.obj (A₂, B₂)}
    {x : P₀ ⟶ Q₀} {y : Q₀ ⟶ T.obj (A₁, B₁)}
    {aM : A₁ ⟶ A₂} {aN : B₁ ⟶ B₂} {iM : A₂ ⟶ A₃} {iN : B₂ ⟶ B₃}
    (hiso : i ≫ μψ = μφ ≫ T.map (iM ×ₘ iN))
    (hcomp : a ≫ μφ = x ≫ y ≫ T.map (aM ×ₘ aN)) :
    (a ≫ i) ≫ μψ = x ≫ y ≫ T.map ((aM ≫ iM) ×ₘ (aN ≫ iN)) := by
  rw [Category.assoc, hiso, reassoc_of% hcomp, ← T.map_comp, prod_comp]

/-- **The composition law of the comparison of Stacks 07A4 along `pullbackCompIso`.** For
morphisms of schemes `p : W ⟶ X` and `f : X ⟶ Y` and `M, N ∈ D(Y_étale, Λ)`, the composite
inverse image `p⁻¹f⁻¹ ≅ (p ≫ f)⁻¹` at `M ⊗^L N` followed by the comparison for `p ≫ f` is
`p⁻¹` of the comparison for `f`, then the comparison for `p`, then `p⁻¹f⁻¹ ≅ (p ≫ f)⁻¹` in each
tensor factor. -/
theorem pullbackCompIso_hom_app_comp_pullbackTensorIso_hom_app {W X Y : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ Y) (M N : DerivedModules Λ Y) :
    (pullbackCompIso Λ p f).hom.app ((Functor.uncurry.obj (tensor Λ Y)).obj (M, N)) ≫
        (pullbackTensorIso Λ (p ≫ f)).hom.app (M, N) =
      (pullback Λ p).map ((pullbackTensorIso Λ f).hom.app (M, N)) ≫
        (pullbackTensorIso Λ p).hom.app ((pullback Λ f).obj M, (pullback Λ f).obj N) ≫
          (Functor.uncurry.obj (tensor Λ W)).map
            ((pullbackCompIso Λ p f).hom.app M ×ₘ (pullbackCompIso Λ p f).hom.app N) := by
  have hp := isMorphismOfSites_ringedToposHom Λ p
  have hf := isMorphismOfSites_ringedToposHom Λ f
  have hpf := RingedToposSiteHom.isMorphismOfSites_comp_u _ _ hp hf
  let := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ W) (Y := ringedTopos Λ Y) ((ringedToposHom Λ f).comp (ringedToposHom Λ p))
    hpf
  have hcomp := Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp
    (ringedToposHom Λ p) (ringedToposHom Λ f) hp hf M N
  have hiso :=
    Sheaves.DerivedPullback.derivedPullbackIsoOfIso_hom_app_comp_derivedPullbackTensorIso_hom_app
      (fSharpCompatible_comp Λ p f) hpf (isMorphismOfSites_ringedToposHom Λ (p ≫ f)) M N
  have hdef : pullbackCompIso Λ p f =
      Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
          (ringedToposHom Λ p) (ringedToposHom Λ f) hp hf ≪≫
        derivedPullbackIsoOfIso (fSharpCompatible_comp Λ p f) := rfl
  rw [hdef]
  simp only [Iso.trans_hom, NatTrans.comp_app]
  exact comp_tensor_algebra (D := DerivedModules Λ W) (T := Functor.uncurry.obj (tensor Λ W))
    (hcomp := hcomp) (hiso := hiso)

/-- The two directions of `pullbackCongr` along an equality and its reverse agree. -/
theorem pullbackCongr_hom_eq_inv_symm {W S : Scheme.{u}} {a b : W ⟶ S} (h : a = b) :
    (pullbackCongr Λ h).hom = (pullbackCongr Λ h.symm).inv := by
  subst h
  rfl

section Square

variable {W X Y S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S) (q : W ⟶ Y) (g : Y ⟶ S)
  (w : p ≫ f = q ≫ g) (E : DerivedModules Λ X) (K : DerivedModules Λ Y)

/-- `kunnethMapOfBaseChange`, unfolded to the abstract maps it is built from. -/
private theorem kunnethMapOfBaseChange_eq_abstract :
    kunnethMapOfBaseChange Λ p f q g w E K =
      adjunctionTensorMap (adjunction Λ f) (Functor.uncurry.obj (tensor Λ S))
          (Functor.uncurry.obj (tensor Λ X)) (pullbackTensorIso Λ f).hom E
          ((pushforward Λ g).obj K) ≫
        (pushforward Λ f).map
          (Stacks.Cohomology.AbstractKunnethMap.tensorBaseChangeMap (adjunction Λ g)
            (adjunction Λ p) (pullback Λ f) (pullback Λ q)
            (pullbackCompIso Λ p f ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ q g).symm)
            (Functor.uncurry.obj (tensor Λ X)) (Functor.uncurry.obj (tensor Λ W))
            (pullbackTensorIso Λ p).hom E K) ≫
          (conjugateIsoEquiv ((adjunction Λ f).comp (adjunction Λ p))
            (adjunction Λ (p ≫ f)) (pullbackCompIso Λ p f).symm).hom.app _ :=
  rfl

/-- `kunnethMap`, unfolded to the abstract Künneth map. -/
private theorem kunnethMap_eq_abstract :
    kunnethMap Λ p f q g w E K =
      Stacks.Cohomology.AbstractKunnethMap.kunnethMap (Functor.uncurry.obj (tensor Λ S))
        (Functor.uncurry.obj (tensor Λ W)) (adjunction Λ f) (adjunction Λ g)
        (adjunction Λ (p ≫ f)) (pullback Λ p) (pullback Λ q) (pullbackTensorIso Λ (p ≫ f)).hom
        (pullbackCompIso Λ p f) (pullbackCompIso Λ q g ≪≫ pullbackCongr Λ w.symm) E K :=
  rfl

/-- The isomorphism `f⁻¹ ⋙ p⁻¹ ≅ q⁻¹ ⋙ ...` of the base change map is the composite of the two
composite inverse images. -/
private theorem baseChangeIso_hom_app (M : DerivedModules Λ S) :
    (pullbackCompIso Λ p f ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ q g).symm).hom.app M =
      (pullbackCompIso Λ p f).hom.app M ≫
        (pullbackCompIso Λ q g ≪≫ pullbackCongr Λ w.symm).inv.app M := by
  have hc : (pullbackCongr Λ w).hom.app M = (pullbackCongr Λ w.symm).inv.app M :=
    congrArg (fun x => NatTrans.app x M) (pullbackCongr_hom_eq_inv_symm Λ w)
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, NatTrans.comp_app,
    NatTrans.comp_app, hc, Iso.symm_hom]

/-- **The map of the proof of [Stacks, Tag 0F1P] is the Künneth map of [Stacks, Tag 0F1E].** For a
commutative square `p ≫ f = q ≫ g` of schemes, `E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`, the
projection formula map, followed by `Rf_*` of the canonical map of Tags 0F1J and 0F1N and by the
composition of direct images, is the Künneth map `Rf_*E ⊗^L Rg_*K ⟶ R(p ≫ f)_*(p⁻¹E ⊗^L q⁻¹K)`.
-/
theorem kunnethMapOfBaseChange_eq_kunnethMap :
    kunnethMapOfBaseChange Λ p f q g w E K = kunnethMap Λ p f q g w E K := by
  rw [kunnethMapOfBaseChange_eq_abstract, kunnethMap_eq_abstract]
  exact (Stacks.Cohomology.AbstractKunnethMap.kunnethMap_eq_projection_tensorBaseChangeMap
    (Functor.uncurry.obj (tensor Λ S)) (Functor.uncurry.obj (tensor Λ X))
    (Functor.uncurry.obj (tensor Λ W)) (adjunction Λ f) (adjunction Λ g) (adjunction Λ p)
    (adjunction Λ (p ≫ f)) (pullback Λ q) (pullbackTensorIso Λ f).hom
    (pullbackTensorIso Λ p).hom (pullbackTensorIso Λ (p ≫ f)).hom (pullbackCompIso Λ p f)
    (pullbackCompIso Λ q g ≪≫ pullbackCongr Λ w.symm)
    (pullbackCompIso Λ p f ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ q g).symm)
    (baseChangeIso_hom_app Λ p f q g w)
    (fun M N => pullbackCompIso_hom_app_comp_pullbackTensorIso_hom_app Λ p f M N) E K).symm

end Square

/-- **The Künneth map of [Stacks, Tag 0F1P] is the Künneth map of [Stacks, Tag 0F1E]**, at the
fibre square of two schemes over `Spec k`. -/
theorem kunnethOverFieldMap_eq_kunnethMap (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (E : DerivedModules Λ X)
    (K : DerivedModules Λ Y) :
    kunnethOverFieldMap Λ k f g E K =
      kunnethMap Λ (Limits.pullback.fst f g) f (Limits.pullback.snd f g) g
        Limits.pullback.condition E K :=
  kunnethMapOfBaseChange_eq_kunnethMap Λ _ _ _ _ _ E K

end Stacks.EtaleCohomology.EtaleCoefficients

end
