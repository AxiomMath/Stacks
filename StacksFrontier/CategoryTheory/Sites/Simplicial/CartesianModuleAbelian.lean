module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianModulePairExactness
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerreModules
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# Equalizers of pairs, and kernels of cartesian modules

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
By Stacks 07TH the cartesian `O`-modules are the pairs `(F, α)` of a module `F` on the
degree-zero component and an isomorphism `α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` satisfying the cocycle
condition on the degree-two component.

This file builds the equalizer of two morphisms of pairs, under the hypothesis that the
pullbacks along the two degree-one faces and along one of the three degree-two faces are left
exact. The equalizer of `f, g : (F, α) ⟶ (G, β)` is the kernel `K` of `f - g` on the degree-zero
modules, with the restriction of `α`; the restriction exists by left exactness of the degree-one
pullbacks, and its cocycle condition is the cocycle condition of `α` cancelled against the
pullback of `K ⟶ F` to the vertex `2` (`f_{δ²₁}^* f_{δ¹₀}^*`, isomorphic to `f_{δ²₀}^* f_{δ¹₀}^*`)
or to the vertex `0` (`f_{δ²₁}^* f_{δ¹₁}^*`, isomorphic to `f_{δ²₂}^* f_{δ¹₁}^*`), one of which
is a monomorphism as soon as one degree-two pullback is left exact. Through the equivalence of
Stacks 07TH the cartesian `O`-modules then have kernels, and form an abelian category.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.equalizerPair`: the equalizer of two
  morphisms of pairs.
* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.equalizerForkIsLimit`: its universal
  property.

## Main results

* `CategoryTheory.ComparisonPair.cocycleTransportMono`: the formal transport of the degree-two
  cocycle condition to a subobject, along a morphism whose image under the middle degree-two
  functor is a monomorphism.
* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.hasEqualizers`: pairs have
  equalizers.
* `CategoryTheory.SimplicialSiteSituation.cartesianModuleSheaf_hasKernels`: cartesian modules
  have kernels.
* `CategoryTheory.SimplicialSiteSituation.cartesianModuleSheafAbelian`: Stacks 0D7K, corrected
  form.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7K](https://stacks.math.columbia.edu/tag/0D7K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites AlgebraicGeometry
open Stacks.SheafOfModules.PushforwardRightExact
open scoped Simplicial

universe u

namespace CategoryTheory

noncomputable section

namespace ComparisonPair

universe w₁ w₂ t₁ t₂

variable {C₁ : Type t₁} [Category.{w₁} C₁] {C₂ : Type t₂} [Category.{w₂} C₂]

/-- Transport of a degree-two cocycle condition to a subobject: the three functors are the
degree-two faces, `i₁ : X₁ ⟶ Y₁` and `i₀ : X₀ ⟶ Y₀` are the two degree-one readings of the
inclusion, and the condition for `αY` cancels to the condition for `αX` once the image of `i₀`
under the middle face `D₁` is a monomorphism. -/
theorem cocycleTransportMono (D₂ D₁ D₀ : C₁ ⥤ C₂) {X₁ X₀ Y₁ Y₀ : C₁}
    (i₁ : X₁ ⟶ Y₁) (i₀ : X₀ ⟶ Y₀)
    (gLX : D₂.obj X₁ ≅ D₁.obj X₁) (gLY : D₂.obj Y₁ ≅ D₁.obj Y₁)
    (gMX : D₂.obj X₀ ≅ D₀.obj X₁) (gMY : D₂.obj Y₀ ≅ D₀.obj Y₁)
    (gRX : D₀.obj X₀ ≅ D₁.obj X₀) (gRY : D₀.obj Y₀ ≅ D₁.obj Y₀)
    (hL : D₂.map i₁ ≫ gLY.hom = gLX.hom ≫ D₁.map i₁)
    (hM : D₂.map i₀ ≫ gMY.hom = gMX.hom ≫ D₀.map i₁)
    (hR : D₀.map i₀ ≫ gRY.hom = gRX.hom ≫ D₁.map i₀)
    (αX : X₁ ⟶ X₀) (αY : Y₁ ⟶ Y₀) (hα : αX ≫ i₀ = i₁ ≫ αY)
    (hmono : Mono (D₁.map i₀))
    (hY : D₁.map αY = gLY.inv ≫ D₂.map αY ≫ gMY.hom ≫ D₀.map αY ≫ gRY.hom) :
    D₁.map αX = gLX.inv ≫ D₂.map αX ≫ gMX.hom ≫ D₀.map αX ≫ gRX.hom := by
  have hL' : gLX.inv ≫ D₂.map i₁ = D₁.map i₁ ≫ gLY.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hL, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have e1 : gRX.hom ≫ D₁.map i₀ = D₀.map i₀ ≫ gRY.hom := hR.symm
  have e2 : D₀.map αX ≫ D₀.map i₀ = D₀.map i₁ ≫ D₀.map αY := by
    rw [← Functor.map_comp, hα, Functor.map_comp]
  have e3 : gMX.hom ≫ D₀.map i₁ = D₂.map i₀ ≫ gMY.hom := hM.symm
  have e4 : D₂.map αX ≫ D₂.map i₀ = D₂.map i₁ ≫ D₂.map αY := by
    rw [← Functor.map_comp, hα, Functor.map_comp]
  rw [← cancel_mono (D₁.map i₀), ← Functor.map_comp, hα, Functor.map_comp, hY]
  simp only [Category.assoc, e1, reassoc_of% e2, reassoc_of% e3, reassoc_of% e4,
    reassoc_of% hL']

/-- Transport of a degree-two cocycle condition to a subobject, cancelling at the other end:
the same statement as `CategoryTheory.ComparisonPair.cocycleTransportMono` for comparison
isomorphisms, under the hypothesis that the image of `i₁` under the middle face `D₁` is a
monomorphism. It is that lemma applied to the inverse cocycle. -/
theorem cocycleTransportMono_left (D₂ D₁ D₀ : C₁ ⥤ C₂) {X₁ X₀ Y₁ Y₀ : C₁}
    (i₁ : X₁ ⟶ Y₁) (i₀ : X₀ ⟶ Y₀)
    (gLX : D₂.obj X₁ ≅ D₁.obj X₁) (gLY : D₂.obj Y₁ ≅ D₁.obj Y₁)
    (gMX : D₂.obj X₀ ≅ D₀.obj X₁) (gMY : D₂.obj Y₀ ≅ D₀.obj Y₁)
    (gRX : D₀.obj X₀ ≅ D₁.obj X₀) (gRY : D₀.obj Y₀ ≅ D₁.obj Y₀)
    (hL : D₂.map i₁ ≫ gLY.hom = gLX.hom ≫ D₁.map i₁)
    (hM : D₂.map i₀ ≫ gMY.hom = gMX.hom ≫ D₀.map i₁)
    (hR : D₀.map i₀ ≫ gRY.hom = gRX.hom ≫ D₁.map i₀)
    (αX : X₁ ⟶ X₀) (αY : Y₁ ⟶ Y₀) [IsIso αX] [IsIso αY] (hα : αX ≫ i₀ = i₁ ≫ αY)
    (hmono : Mono (D₁.map i₁))
    (hY : D₁.map αY = gLY.inv ≫ D₂.map αY ≫ gMY.hom ≫ D₀.map αY ≫ gRY.hom) :
    D₁.map αX = gLX.inv ≫ D₂.map αX ≫ gMX.hom ≫ D₀.map αX ≫ gRX.hom := by
  have hM' : D₀.map i₁ ≫ gMY.inv = gMX.inv ≫ D₂.map i₀ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hM, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hα' : inv αX ≫ i₁ = i₀ ≫ inv αY := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hα, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hY' : D₁.map (inv αY) =
      gRY.inv ≫ D₀.map (inv αY) ≫ gMY.inv ≫ D₂.map (inv αY) ≫ gLY.hom := by
    rw [← cancel_epi (D₁.map αY)]
    conv_rhs => rw [hY]
    simp [Functor.map_inv]
  have h := cocycleTransportMono D₀ D₁ D₂ i₀ i₁ gRX gRY gMX.symm gMY.symm gLX gLY hR hM' hL
    (inv αX) (inv αY) hα' hmono hY'
  rw [← cancel_mono (D₁.map (inv αX))]
  conv_rhs => rw [h]
  simp [Functor.map_inv]

end ComparisonPair

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The pullback of sheaves of modules along a simplicial transition is additive. -/
instance componentModulePullback_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModulePullback O φ).Additive :=
  AlgebraicGeometry.RingedToposHom.pullbackModules_additive (S.transitionRingedToposHom O φ)

/-- Naturality of the left identification of the cocycle condition. -/
theorem glueModulesLeft_naturality {F F' : (S.componentRingedTopos O ⦋0⦌).Modules}
    (g : F ⟶ F') :
    (S.componentModulePullback O (SimplexCategory.δ (2 : Fin 3))).map
        ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map g) ≫
        (S.glueModulesLeft O F').hom =
      (S.glueModulesLeft O F).hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).map
          ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map g) := by
  have h := S.glueModulesOfEq_naturality O (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (1 : Fin 3))
    _ SimplexCategory.delta_one_comp_delta_two SimplexCategory.delta_one_comp_delta_one g
  have e : ∀ X, S.glueModulesLeft O X = S.glueModulesOfEq O (SimplexCategory.δ (1 : Fin 2))
      (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3))
      (SimplexCategory.δ (1 : Fin 3)) _ SimplexCategory.delta_one_comp_delta_two
      SimplexCategory.delta_one_comp_delta_one X :=
    fun _ => rfl
  rw [e, e]
  exact h

/-- Naturality of the middle identification of the cocycle condition. -/
theorem glueModulesMiddle_naturality {F F' : (S.componentRingedTopos O ⦋0⦌).Modules}
    (g : F ⟶ F') :
    (S.componentModulePullback O (SimplexCategory.δ (2 : Fin 3))).map
        ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map g) ≫
        (S.glueModulesMiddle O F').hom =
      (S.glueModulesMiddle O F).hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 3))).map
          ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map g) := by
  have h := S.glueModulesOfEq_naturality O (SimplexCategory.δ (0 : Fin 2))
    (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (0 : Fin 3))
    _ SimplexCategory.delta_zero_comp_delta_two SimplexCategory.delta_one_comp_delta_zero g
  have e : ∀ X, S.glueModulesMiddle O X = S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2))
      (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3))
      (SimplexCategory.δ (0 : Fin 3)) _ SimplexCategory.delta_zero_comp_delta_two
      SimplexCategory.delta_one_comp_delta_zero X :=
    fun _ => rfl
  rw [e, e]
  exact h

/-- Naturality of the right identification of the cocycle condition. -/
theorem glueModulesRight_naturality {F F' : (S.componentRingedTopos O ⦋0⦌).Modules}
    (g : F ⟶ F') :
    (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 3))).map
        ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map g) ≫
        (S.glueModulesRight O F').hom =
      (S.glueModulesRight O F).hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).map
          ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map g) := by
  have h := S.glueModulesOfEq_naturality O (SimplexCategory.δ (0 : Fin 2))
    (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.δ (1 : Fin 3))
    _ SimplexCategory.delta_zero_comp_delta_zero SimplexCategory.delta_zero_comp_delta_one g
  have e : ∀ X, S.glueModulesRight O X = S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2))
      (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3))
      (SimplexCategory.δ (1 : Fin 3)) _ SimplexCategory.delta_zero_comp_delta_zero
      SimplexCategory.delta_zero_comp_delta_one X :=
    fun _ => rfl
  rw [e, e]
  exact h

/-- The cocycle condition passes to a subobject: if `ι : K ⟶ F` carries a comparison
isomorphism `αK` of `K` to the comparison isomorphism `α` of `F`, and the pullback of `ι` along
the vertex `δ¹₀ ≫ δ²₁` is a monomorphism, then `αK` satisfies the cocycle condition as soon as
`α` does. -/
theorem isModuleCocycle_of_mono {K F : (S.componentRingedTopos O ⦋0⦌).Modules} (ι : K ⟶ F)
    (αK : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (α : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F)
    (hα : αK.hom ≫ (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map ι =
      (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map ι ≫ α.hom)
    (hmono : Mono ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).map
      ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map ι)))
    (hF : S.IsModuleCocycle O F α) : S.IsModuleCocycle O K αK := by
  unfold IsModuleCocycle at hF ⊢
  exact ComparisonPair.cocycleTransportMono _ _ _ _ _ _ _ _ _ _ _
    (S.glueModulesLeft_naturality O ι) (S.glueModulesMiddle_naturality O ι)
    (S.glueModulesRight_naturality O ι) αK.hom α.hom hα hmono hF

/-- The cocycle condition passes to a subobject, cancelling at the vertex `δ¹₁ ≫ δ²₁`: the
same statement as `CategoryTheory.SimplicialSiteSituation.isModuleCocycle_of_mono`, under the
hypothesis that the pullback of `ι` along that vertex is a monomorphism. -/
theorem isModuleCocycle_of_mono_left {K F : (S.componentRingedTopos O ⦋0⦌).Modules} (ι : K ⟶ F)
    (αK : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj K ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj K)
    (α : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F)
    (hα : αK.hom ≫ (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map ι =
      (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map ι ≫ α.hom)
    (hmono : Mono ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).map
      ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map ι)))
    (hF : S.IsModuleCocycle O F α) : S.IsModuleCocycle O K αK := by
  unfold IsModuleCocycle at hF ⊢
  exact ComparisonPair.cocycleTransportMono_left _ _ _ _ _ _ _ _ _ _ _
    (S.glueModulesLeft_naturality O ι) (S.glueModulesMiddle_naturality O ι)
    (S.glueModulesRight_naturality O ι) αK.hom α.hom hα hmono hF

/-- At least one of the three pullbacks of modules along the degree-two faces
`δ²₀, δ²₁, δ²₂ : [1] ⟶ [2]` is left exact. -/
abbrev DegreeTwoFaceLeftExact : Prop :=
  PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 3))) ∨
    PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))) ∨
    PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (2 : Fin 3)))

namespace CartesianModulePair

section Equalizer

variable [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2)))]
  [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2)))]
  [Fact (S.DegreeTwoFaceLeftExact O)]
  {A B : CartesianModulePair S O} (f g : A ⟶ B)

omit [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2)))]
  [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2)))]
  [Fact (S.DegreeTwoFaceLeftExact O)] in
/-- The difference of two morphisms of pairs commutes with the comparison isomorphisms. -/
theorem sub_comm :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map (f.map - g.map) ≫
        B.iso.hom =
      A.iso.hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map (f.map - g.map) := by
  rw [Functor.map_sub, Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub, f.comm,
    g.comm]

/-- The comparison isomorphism on the equalizer of two morphisms of pairs. -/
def equalizerIso :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj
        (kernel (f.map - g.map)) ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj
        (kernel (f.map - g.map)) :=
  ComparisonPair.kernelIso _ _ (f.map - g.map) A.iso B.iso (sub_comm S O f g)

omit [Fact (S.DegreeTwoFaceLeftExact O)] in
/-- The comparison isomorphism on the equalizer is compatible with its inclusion into `A`. -/
theorem equalizerIso_hom_comp :
    (equalizerIso S O f g).hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map
          (kernel.ι (f.map - g.map)) =
      (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map
          (kernel.ι (f.map - g.map)) ≫ A.iso.hom :=
  ComparisonPair.kernelIso_hom_comp _ _ _ _ _ _

/-- If `a ≫ i.hom = j.hom ≫ b` with `i` and `j` isomorphisms and `a` a monomorphism, then `b` is a
monomorphism. -/
private theorem mono_of_comp_eq_iso_comp {C : Type*} [Category C] {X Y X' Y' : C} {a : X ⟶ Y}
    {b : X' ⟶ Y'} (i : Y ≅ Y') (j : X ≅ X') (e : a ≫ i.hom = j.hom ≫ b) [Mono a] : Mono b := by
  rw [show b = j.inv ≫ a ≫ i.hom by rw [e, Iso.inv_hom_id_assoc]]
  infer_instance

/-- The comparison isomorphism on the equalizer satisfies the cocycle condition. -/
theorem equalizerIso_cocycle :
    S.IsModuleCocycle O (kernel (f.map - g.map)) (equalizerIso S O f g) := by
  have h₁ := ComparisonPair.mono_map_kernel_ι
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))) (f.map - g.map)
  have h₀ := ComparisonPair.mono_map_kernel_ι
    (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))) (f.map - g.map)
  rcases (Fact.out : S.DegreeTwoFaceLeftExact O) with h | h | h
  · have := h
    exact S.isModuleCocycle_of_mono O (kernel.ι (f.map - g.map)) (equalizerIso S O f g) A.iso
      (equalizerIso_hom_comp S O f g)
      (mono_of_comp_eq_iso_comp _ _ (S.glueModulesRight_naturality O (kernel.ι (f.map - g.map))))
      A.cocycle
  · have := h
    exact S.isModuleCocycle_of_mono O (kernel.ι (f.map - g.map)) (equalizerIso S O f g) A.iso
      (equalizerIso_hom_comp S O f g) inferInstance A.cocycle
  · have := h
    exact S.isModuleCocycle_of_mono_left O (kernel.ι (f.map - g.map)) (equalizerIso S O f g)
      A.iso (equalizerIso_hom_comp S O f g)
      (mono_of_comp_eq_iso_comp _ _ (S.glueModulesLeft_naturality O (kernel.ι (f.map - g.map))))
      A.cocycle

/-- The equalizer of two morphisms of pairs. -/
abbrev equalizerPair : CartesianModulePair S O where
  module := kernel (f.map - g.map)
  iso := equalizerIso S O f g
  cocycle := equalizerIso_cocycle S O f g

/-- The inclusion of the equalizer. -/
def equalizerι : equalizerPair S O f g ⟶ A where
  map := kernel.ι (f.map - g.map)
  comm := (equalizerIso_hom_comp S O f g).symm

/-- The underlying morphism of degree-zero modules of the inclusion of the equalizer. -/
theorem equalizerι_map : (equalizerι S O f g).map = kernel.ι (f.map - g.map) := rfl

/-- The inclusion of the equalizer equalizes the two morphisms of pairs. -/
theorem equalizerι_condition : equalizerι S O f g ≫ f = equalizerι S O f g ≫ g := by
  apply hom_ext
  simpa only [comp_map, equalizerι_map, Preadditive.comp_sub, sub_eq_zero] using
    kernel.condition (f.map - g.map)

/-- The equalizer fork. -/
def equalizerFork : Fork f g := Fork.ofι (equalizerι S O f g) (equalizerι_condition S O f g)

omit [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2)))]
  [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2)))]
  [Fact (S.DegreeTwoFaceLeftExact O)] in
/-- A morphism equalizing `f` and `g` is killed by `f.map - g.map` in degree zero. -/
theorem lift_w {Z : CartesianModulePair S O} (h : Z ⟶ A) (hh : h ≫ f = h ≫ g) :
    h.map ≫ (f.map - g.map) = 0 := by
  rw [Preadditive.comp_sub, sub_eq_zero]
  exact congrArg Hom.map hh

omit [Fact (S.DegreeTwoFaceLeftExact O)] in
/-- The lift to the kernel of a morphism equalizing `f` and `g` commutes with the comparison
isomorphisms. -/
theorem lift_comm {Z : CartesianModulePair S O} (h : Z ⟶ A) (hh : h ≫ f = h ≫ g) :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map
        (kernel.lift _ h.map (lift_w S O f g h hh)) ≫ (equalizerIso S O f g).hom =
      Z.iso.hom ≫ (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map
        (kernel.lift _ h.map (lift_w S O f g h hh)) := by
  have := ComparisonPair.mono_map_kernel_ι
    (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))) (f.map - g.map)
  rw [← cancel_mono ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map
    (kernel.ι (f.map - g.map)))]
  simp only [Category.assoc]
  rw [equalizerIso_hom_comp, ← Functor.map_comp_assoc, ← Functor.map_comp, kernel.lift_ι]
  exact h.comm

/-- The lift of a morphism equalizing `f` and `g` to the equalizer. -/
def equalizerLift {Z : CartesianModulePair S O} (h : Z ⟶ A) (hh : h ≫ f = h ≫ g) :
    Z ⟶ equalizerPair S O f g :=
  Hom.mk (B := equalizerPair S O f g) (kernel.lift (f.map - g.map) h.map (lift_w S O f g h hh))
    (lift_comm S O f g h hh)

/-- The lift to the equalizer followed by the inclusion is the original morphism. -/
theorem equalizerLift_ι {Z : CartesianModulePair S O} (h : Z ⟶ A) (hh : h ≫ f = h ≫ g) :
    equalizerLift S O f g h hh ≫ equalizerι S O f g = h :=
  hom_ext S O (kernel.lift_ι _ _ _)

/-- The equalizer fork is a limit. -/
def equalizerForkIsLimit : IsLimit (equalizerFork S O f g) :=
  Fork.IsLimit.mk _ (fun s => equalizerLift S O f g s.ι s.condition)
    (fun s => equalizerLift_ι S O f g s.ι s.condition)
    (fun s m hm => hom_ext S O (by
      change m.map = kernel.lift (f.map - g.map) s.ι.map (lift_w S O f g s.ι s.condition)
      apply (cancel_mono (kernel.ι (f.map - g.map))).1
      rw [kernel.lift_ι]
      exact congrArg Hom.map hm))

/-- Two morphisms of pairs have an equalizer. -/
instance hasLimit_parallelPair : HasLimit (parallelPair f g) :=
  ⟨⟨⟨_, equalizerForkIsLimit S O f g⟩⟩⟩

omit f g in
/-- Pairs have equalizers when the degree-one pullbacks and one degree-two pullback are left
exact. -/
instance hasEqualizers : HasEqualizers (CartesianModulePair S O) :=
  hasEqualizers_of_hasLimit_parallelPair _

end Equalizer

/-- The module of degree zero of a pair, as a functor. -/
@[simps]
def forget : CartesianModulePair S O ⥤ (S.componentRingedTopos O ⦋0⦌).Modules where
  obj A := A.module
  map f := f.map

/-- A morphism of pairs whose morphism of degree-zero modules is invertible is invertible. -/
instance forget_reflectsIsomorphisms : (forget S O).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    have : IsIso f.map := hf
    exact (isoMk S O (asIso f.map) f.comm).isIso_hom

section Equalizer

variable [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2)))]
  [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2)))]
  [Fact (S.DegreeTwoFaceLeftExact O)]
  {A B : CartesianModulePair S O} (f g : A ⟶ B)

/-- The degree-zero module of the equalizer of two morphisms of pairs is their equalizer. -/
def forgetEqualizerForkIsLimit : IsLimit ((forget S O).mapCone (equalizerFork S O f g)) :=
  (isLimitMapConeForkEquiv (forget S O) (equalizerι_condition S O f g)).invFun
    (Preadditive.isLimitForkOfKernelFork
      (c := KernelFork.ofι (kernel.ι (f.map - g.map)) (kernel.condition _))
      (kernelIsKernel (f.map - g.map)))

/-- Forgetting to degree zero preserves the equalizer of two morphisms of pairs. -/
instance forget_preservesLimit_parallelPair : PreservesLimit (parallelPair f g) (forget S O) :=
  preservesLimit_of_preserves_limit_cone (equalizerForkIsLimit S O f g)
    (forgetEqualizerForkIsLimit S O f g)

omit f g in
/-- Forgetting to degree zero preserves equalizers. -/
instance forget_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (forget S O) where
  preservesLimit {K} := preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

end Equalizer

end CartesianModulePair

section Abelian

attribute [local instance] hasSheafifyTotalModule wEqualsLocallyBijectiveTotalModule
  preservesFiniteColimits_componentModuleRestriction

local instance componentModuleRestriction_additive' (n : SimplexCategory) :
    (S.componentModuleRestriction (S.totalRingSheaf O) n).Additive := ⟨rfl⟩

/-- The degree-zero restriction of cartesian modules. -/
def cartesianDegreeZero : S.CartesianModuleSheaf O ⥤ (S.componentRingedTopos O ⦋0⦌).Modules :=
  ObjectProperty.ι (S.IsCartesianModule O) ⋙ S.componentModuleRestriction (S.totalRingSheaf O) ⦋0⦌

/-- The degree-zero restriction is the pair functor of Stacks 07TH followed by forgetting the
comparison isomorphism. -/
def cartesianDegreeZeroIso :
    S.cartesianModulePairFunctor O ⋙ CartesianModulePair.forget S O ≅ S.cartesianDegreeZero O :=
  NatIso.ofComponents (fun M => Iso.refl ((S.cartesianDegreeZero O).obj M)) (fun _ => by
    simp only [Iso.refl_hom]; rfl)

/-- The degree-zero restriction of cartesian modules is additive. -/
instance cartesianDegreeZero_additive : (S.cartesianDegreeZero O).Additive := ⟨rfl⟩

/-- The degree-zero restriction of cartesian modules reflects isomorphisms. -/
instance cartesianDegreeZero_reflectsIsomorphisms :
    (S.cartesianDegreeZero O).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have : IsIso ((S.cartesianModulePairFunctor O ⋙ CartesianModulePair.forget S O).map f) := hf
    exact isIso_of_reflects_iso f (S.cartesianModulePairFunctor O ⋙ CartesianModulePair.forget S O)

/-- Cartesian modules are closed under coequalizers in `Mod(O)`. -/
instance isCartesianModule_isClosedUnderColimitsOfShape_parallelPair :
    ObjectProperty.IsClosedUnderColimitsOfShape (S.IsCartesianModule O) WalkingParallelPair :=
  S.isCartesianModule_isClosedUnderColimitsOfShape O WalkingParallelPair

/-- Cartesian modules are closed under finite coproducts in `Mod(O)`. -/
instance isCartesianModule_isClosedUnderColimitsOfShape_discrete (n : ℕ) :
    ObjectProperty.IsClosedUnderColimitsOfShape (S.IsCartesianModule O) (Discrete (Fin n)) :=
  S.isCartesianModule_isClosedUnderColimitsOfShape O (Discrete (Fin n))

/-- Cartesian modules have coequalizers, computed in `Mod(O)`. -/
instance cartesianModuleSheaf_hasCoequalizers : HasCoequalizers (S.CartesianModuleSheaf O) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (ObjectProperty.ι (S.IsCartesianModule O))

/-- Cartesian modules have cokernels. -/
instance cartesianModuleSheaf_hasCokernels : HasCokernels (S.CartesianModuleSheaf O) :=
  hasCokernels_of_hasCoequalizers _

/-- Cartesian modules have finite products: they are closed under finite coproducts in `Mod(O)`,
which are biproducts. -/
instance cartesianModuleSheaf_hasFiniteProducts : HasFiniteProducts (S.CartesianModuleSheaf O) :=
  have : HasFiniteCoproducts (S.CartesianModuleSheaf O) := ⟨fun _ =>
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (ObjectProperty.ι (S.IsCartesianModule O))⟩
  have : HasFiniteBiproducts (S.CartesianModuleSheaf O) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  inferInstance

/-- The degree-zero restriction of cartesian modules preserves coequalizers. -/
instance cartesianDegreeZero_preservesCoequalizers :
    PreservesColimitsOfShape WalkingParallelPair (S.cartesianDegreeZero O) := by
  have := createsColimitsOfShapeFullSubcategoryInclusion WalkingParallelPair
    (S.IsCartesianModule O)
  have h1 : PreservesColimitsOfShape WalkingParallelPair
      (ObjectProperty.ι (S.IsCartesianModule O)) := inferInstance
  have h2 : PreservesColimitsOfShape WalkingParallelPair
      (S.componentModuleRestriction (S.totalRingSheaf O) ⦋0⦌) :=
    (preservesFiniteColimits_componentModuleRestriction S O ⦋0⦌).preservesFiniteColimits _
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h1 h2

variable [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2)))]
  [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2)))]
  [Fact (S.DegreeTwoFaceLeftExact O)]

/-- Cartesian modules have equalizers, transported from those of pairs along Stacks 07TH. -/
instance cartesianModuleSheaf_hasEqualizers : HasEqualizers (S.CartesianModuleSheaf O) :=
  Adjunction.hasLimitsOfShape_of_equivalence (S.cartesianModulePairFunctor O)

/-- Cartesian modules have kernels. -/
instance cartesianModuleSheaf_hasKernels : HasKernels (S.CartesianModuleSheaf O) :=
  hasKernels_of_hasEqualizers _

/-- The degree-zero restriction of cartesian modules preserves equalizers. -/
instance cartesianDegreeZero_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (S.cartesianDegreeZero O) :=
  preservesLimitsOfShape_of_natIso (S.cartesianDegreeZeroIso O)

/-- The coimage-image comparison of a morphism of cartesian modules is an isomorphism: it is one
after the degree-zero restriction, which preserves kernels and cokernels and reflects
isomorphisms, and modules on the degree-zero component form an abelian category. -/
theorem cartesianModuleSheaf_isIso_coimageImageComparison {M N : S.CartesianModuleSheaf O}
    (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  have h := Abelian.PreservesCoimageImageComparison.iso (S.cartesianDegreeZero O) f
  have : IsIso ((S.cartesianDegreeZero O).map (Abelian.coimageImageComparison f)) :=
    (Arrow.isIso_iff_isIso_of_isIso h.hom).2 inferInstance
  exact isIso_of_reflects_iso _ (S.cartesianDegreeZero O)

/-- The cartesian `O`-modules form an abelian category as soon as the pullbacks of modules along
the two degree-one faces and along one of the three degree-two faces are left exact. -/
abbrev cartesianModuleSheafAbelianOfLeftExact : Abelian (S.CartesianModuleSheaf O) :=
  have := fun {X Y : S.CartesianModuleSheaf O} (f : X ⟶ Y) =>
    S.cartesianModuleSheaf_isIso_coimageImageComparison O f
  Abelian.ofCoimageImageComparisonIsIso

omit [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2)))]
  [PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2)))]
  [Fact (S.DegreeTwoFaceLeftExact O)] in
/-- **Stacks 0D7K, corrected form.** If the morphisms of ringed topoi `f_{δ¹₁}` and `f_{δ¹₀}` are
flat, and so is one of the three degree-two faces `f_{δ²₀}`, `f_{δ²₁}`, `f_{δ²₂}`, then the
cartesian `O`-modules form an abelian category, with the additive structure of `Mod(O)`; its
cokernels are those of `Mod(O)`, and its kernels are those of the pairs of Stacks 07TH, computed
in degree zero.

The source asserts this under flatness of `f_{δ¹₁}` and `f_{δ¹₀}` alone, which is false: see
`CategoryTheory.PointSimplicialSite.RatioCounterexample.exists_not_abelian_cartesianModuleSheaf`.
The kernel of a morphism of pairs carries the restricted comparison isomorphism, but its cocycle
condition lives on the degree-two component; it can be cancelled against the pullback of the
kernel inclusion to the vertex `2` (through `δ²₁` or `δ²₀`) or to the vertex `0` (through `δ²₁`
or `δ²₂`), which is a monomorphism as soon as one degree-two face is flat. -/
@[stacks 0D7K "corrected form of the positive assertion, which is false as written (the source's hypothesis, flatness of f_{δ¹₁} and f_{δ¹₀} alone, does not suffice: see CategoryTheory.PointSimplicialSite.RatioCounterexample.exists_not_abelian_cartesianModuleSheaf); with one of f_{δ²₀}, f_{δ²₁}, f_{δ²₂} flat as well the cartesian O-modules form an abelian category, with the additive structure of Mod(O)"]
abbrev cartesianModuleSheafAbelian
    (h₁ : (S.transitionRingedToposHom O (SimplexCategory.δ (1 : Fin 2))).IsFlat)
    (h₀ : (S.transitionRingedToposHom O (SimplexCategory.δ (0 : Fin 2))).IsFlat)
    (h₂ : ∃ i : Fin 3, (S.transitionRingedToposHom O (SimplexCategory.δ i)).IsFlat) :
    Abelian (S.CartesianModuleSheaf O) :=
  have : PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))) :=
    S.preservesFiniteLimits_transitionPullbackModules_of_isFlat O _ h₁
  have : PreservesFiniteLimits (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))) :=
    S.preservesFiniteLimits_transitionPullbackModules_of_isFlat O _ h₀
  have : Fact (S.DegreeTwoFaceLeftExact O) := ⟨by
    obtain ⟨i, hi⟩ := h₂
    have := S.preservesFiniteLimits_transitionPullbackModules_of_isFlat O _ hi
    fin_cases i
    · exact Or.inl this
    · exact Or.inr (Or.inl this)
    · exact Or.inr (Or.inr this)⟩
  S.cartesianModuleSheafAbelianOfLeftExact O

end Abelian

end SimplicialSiteSituation

end

end CategoryTheory

end
