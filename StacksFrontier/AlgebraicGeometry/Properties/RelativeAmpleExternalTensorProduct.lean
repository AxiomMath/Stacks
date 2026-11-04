module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic

/-!
# The external tensor product of relatively ample modules

For schemes `X` and `Y` over a base `S`, an `f`-ample invertible module `L` on `X` and a
`g`-ample invertible module `N` on `Y`, the external tensor product `pr₁^* L ⊗ pr₂^* N` on
`X ×_S Y` is ample relative to `X ×_S Y ⟶ S`. This is Stacks Tag 0DNK read relative to the
base: over an affine open `V` of `S` the preimage of `V` in `X ×_S Y` is `f⁻¹V ×_V g⁻¹V`, where
Tag 0DNK applies with the affine, hence quasi-separated, base `V`.

## Main definitions

* `Stacks.AmpleExternalTensor.pullbackExternalTensorIso`: the pullback of `pr₁^* L ⊗ pr₂^* N`
  along a morphism `φ` into `X ×_S Y` is `(φ ≫ pr₁)^* L ⊗ (φ ≫ pr₂)^* N`.

## Main results

* `Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor`: the external tensor product of
  an `f`-ample and a `g`-ample invertible module is ample relative to `X ×_S Y ⟶ S`.
* `Stacks.AmpleExternalTensor.isRelativelyAmple_tensorModules_of_isPullback`: the same for any
  cartesian square in place of the chosen fibre product.

## References

* [Stacks Project, Tag 0DNK](https://stacks.math.columbia.edu/tag/0DNK)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.RelativeVeryAmple
open Stacks.AmpleLocallyClosed (pullbackModule)

namespace Stacks.AmpleExternalTensor

universe u

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The pullback of the external tensor product `pr₁^* L ⊗ pr₂^* N` along a morphism
`φ : W ⟶ X ×_S Y` is `(φ ≫ pr₁)^* L ⊗ (φ ≫ pr₂)^* N`: pullback commutes with the tensor product
and with composition. -/
def pullbackExternalTensorIso {W : Scheme.{u}} (φ : W ⟶ pullback f g) (L : X.Modules)
    (N : Y.Modules) :
    (modulePullback φ.toLRSHom.toShHom).obj (externalTensor f g L N) ≅
      tensorModules W ((modulePullback (φ ≫ pullback.fst f g).toLRSHom.toShHom).obj L)
        ((modulePullback (φ ≫ pullback.snd f g).toLRSHom.toShHom).obj N) :=
  pullbackTensorModulesIso φ _ _ ≪≫
    tensorModulesMapIso W ((Scheme.Modules.pullbackComp φ (pullback.fst f g)).app L)
      ((Scheme.Modules.pullbackComp φ (pullback.snd f g)).app N)

/-- The preimage of an open `V` of the base in `X ×_S Y` is the range of the open immersion
`f⁻¹V ×_V g⁻¹V ⟶ X ×_S Y`. -/
theorem opensRange_pullbackMap_morphismRestrict (V : S.Opens) :
    (pullback.map (f ∣_ V) (g ∣_ V) f g (f ⁻¹ᵁ V).ι (g ⁻¹ᵁ V).ι V.ι
        (morphismRestrict_ι f V) (morphismRestrict_ι g V)).opensRange =
      (pullback.fst f g ≫ f) ⁻¹ᵁ V := by
  apply TopologicalSpace.Opens.ext
  show Set.range _ = _
  rw [Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  ext w
  have hw : g (pullback.snd f g w) = f (pullback.fst f g w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  show f (pullback.fst f g w) ∈ V ∧ g (pullback.snd f g w) ∈ V ↔
    (pullback.fst f g ≫ f) w ∈ V
  rw [Scheme.Hom.comp_apply, hw]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- Pulling back `i^* M` along `a` is pulling back `M` along any `c` equal to `a ≫ i`. -/
private def pullbackPullbackModuleIso {P Q Z : Scheme.{u}} (a : P ⟶ Q) (i : Q ⟶ Z) {c : P ⟶ Z}
    (h : a ≫ i = c) (M : Z.Modules) :
    (modulePullback a.toLRSHom.toShHom).obj (pullbackModule i M) ≅
      (modulePullback c.toLRSHom.toShHom).obj M :=
  (Scheme.Modules.pullbackComp a i).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

variable (L : X.Modules) (N : Y.Modules) [IsInvertibleModule X L] [IsInvertibleModule Y N]

/-- **Stacks Tag 0DNK, relative to the base.** For schemes `X` and `Y` over a base `S`, an
invertible `𝒪_X`-module `L` ample relative to `f : X ⟶ S` and an invertible `𝒪_Y`-module `N`
ample relative to `g : Y ⟶ S`, the external tensor product `pr₁^* L ⊗ pr₂^* N` is ample relative
to `X ×_S Y ⟶ S`. No hypothesis on `S`.

The morphism is quasi-compact as a base change of `g` followed by `f`. Over an affine open `V` of
`S` the preimage of `V` is the range of the open immersion `f⁻¹V ×_V g⁻¹V ⟶ X ×_S Y`, where the
external tensor product of the two restrictions is ample by Tag 0DNK
(`Stacks.AmpleExternalTensor.isAmple_externalTensor`), the affine base `V` being
quasi-separated; the restriction of `pr₁^* L ⊗ pr₂^* N` is its transport along the
identification. -/
theorem isRelativelyAmple_externalTensor (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (pullback.fst f g ≫ f) (externalTensor f g L N) := by
  have hf : QuasiCompact f := hL.1
  have hg : QuasiCompact g := hN.1
  refine ⟨inferInstance, fun V hV => ?_⟩
  have : IsAffine V := hV
  let LV := pullbackModule (f ⁻¹ᵁ V).ι L
  let NV := pullbackModule (g ⁻¹ᵁ V).ι N
  have hP : IsAmple (pullback (f ∣_ V) (g ∣_ V)) (externalTensor (f ∣_ V) (g ∣_ V) LV NV) :=
    isAmple_externalTensor (f ∣_ V) (g ∣_ V) LV NV (hL.2 V hV) (hN.2 V hV)
  let φ := pullback.map (f ∣_ V) (g ∣_ V) f g (f ⁻¹ᵁ V).ι (g ⁻¹ᵁ V).ι V.ι
    (morphismRestrict_ι f V) (morphismRestrict_ι g V)
  let ε : ((pullback.fst f g ≫ f) ⁻¹ᵁ V).toScheme ≅ pullback (f ∣_ V) (g ∣_ V) :=
    ((Scheme.Hom.isoOpensRange φ) ≪≫
      (pullback f g).isoOfEq (opensRange_pullbackMap_morphismRestrict f g V)).symm
  have hε : ε.hom ≫ φ = ((pullback.fst f g ≫ f) ⁻¹ᵁ V).ι := by
    have h₀ : (Scheme.Hom.isoOpensRange φ).inv ≫ φ = φ.opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    simp only [ε, Iso.symm_hom, Iso.trans_inv, Category.assoc]
    rw [h₀, Scheme.isoOfEq_inv_ι]
  have hamp := Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso ε.hom _ hP
  refine (isAmple_congr _ _ ?_).mp hamp
  have h₁ : (ε.hom ≫ pullback.fst (f ∣_ V) (g ∣_ V)) ≫ (f ⁻¹ᵁ V).ι =
      ((pullback.fst f g ≫ f) ⁻¹ᵁ V).ι ≫ pullback.fst f g := by
    rw [← hε, Category.assoc, Category.assoc, pullback.lift_fst]
  have h₂ : (ε.hom ≫ pullback.snd (f ∣_ V) (g ∣_ V)) ≫ (g ⁻¹ᵁ V).ι =
      ((pullback.fst f g ≫ f) ⁻¹ᵁ V).ι ≫ pullback.snd f g := by
    rw [← hε, Category.assoc, Category.assoc, pullback.lift_snd]
  refine pullbackExternalTensorIso (f ∣_ V) (g ∣_ V) ε.hom LV NV ≪≫
    tensorModulesMapIso _ ?_ ?_ ≪≫
      (pullbackExternalTensorIso f g ((pullback.fst f g ≫ f) ⁻¹ᵁ V).ι L N).symm
  · exact pullbackPullbackModuleIso _ _ h₁ L
  · exact pullbackPullbackModuleIso _ _ h₂ N

/-- The tensor product of the pullbacks of two invertible modules is invertible. -/
instance isInvertibleModule_tensorModules_modulePullback {P : Scheme.{u}} (a : P ⟶ X)
    (b : P ⟶ Y) :
    IsInvertibleModule P (tensorModules P ((modulePullback a.toLRSHom.toShHom).obj L)
      ((modulePullback b.toLRSHom.toShHom).obj N)) :=
  Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules P _ _

/-- **Stacks Tag 0DNK relative to the base, on any cartesian square.** For a cartesian square
`P ⟶ X`, `P ⟶ Y` over `f : X ⟶ S` and `g : Y ⟶ S`, an `f`-ample invertible `L` and a `g`-ample
invertible `N`, the module `a^* L ⊗ b^* N` on `P` is ample relative to `a ≫ f : P ⟶ S`. This is
`Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor` transported along the
isomorphism of `P` with the chosen fibre product. -/
theorem isRelativelyAmple_tensorModules_of_isPullback {P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    (h : IsPullback a b f g) (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (a ≫ f)
      (tensorModules P ((modulePullback a.toLRSHom.toShHom).obj L)
        ((modulePullback b.toLRSHom.toShHom).obj N)) := by
  have key := Stacks.AmpleBridge.isRelativelyAmple_comp_of_isIso h.isoPullback.hom
    (pullback.fst f g ≫ f) (externalTensor f g L N)
    (isRelativelyAmple_externalTensor f g L N hL hN)
  rw [← Category.assoc, h.isoPullback_hom_fst] at key
  refine (isRelativelyAmple_congr _ _ _ ?_).mp key
  exact pullbackExternalTensorIso f g h.isoPullback.hom L N ≪≫
    tensorModulesMapIso P ((Scheme.Modules.pullbackCongr h.isoPullback_hom_fst).app L)
      ((Scheme.Modules.pullbackCongr h.isoPullback_hom_snd).app N)

end Stacks.AmpleExternalTensor

end
