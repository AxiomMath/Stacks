module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.SheafyTrace

/-!
# The map `Rf_*RHom(L, Rf^!K) ⟶ RHom(Rf_!L, K)` is invertible once the projection map is

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes, `Λ` a torsion ring and `Rf^!` a right adjoint of `Rf_!`. The proof of
[Stacks, Tag 0GLC] shows that the map

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`

of [Stacks, Tag 0GLB] is an isomorphism by checking that it induces a bijection on
`Hom_Y(M, -)` for every `M`, through the string of equalities

```
Hom_Y(M, Rf_*RHom(L, Rf^!K)) = Hom_X(f^{-1}M, RHom(L, Rf^!K))      (Tag 07A6)
                             = Hom_X(f^{-1}M ⊗^L L, Rf^!K)          (Tag 08J9)
                             = Hom_Y(Rf_!(f^{-1}M ⊗^L L), K)         (Rf_! ⊣ Rf^!)
                             = Hom_Y(M ⊗^L Rf_!L, K)                 (Tag 0GL5)
                             = Hom_Y(M, RHom(Rf_!L, K))             (Tag 08J9)
```

This file carries out that argument at the abstract compactification data of
`Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData`, over which the map of
[Stacks, Tag 0GLB] (`CompactificationData.sheafyTrace`) is defined. What the source leaves
implicit is that the composite of the five bijections is composition with the map of
[Stacks, Tag 0GLB]; this holds for one specific identification
`M ⊗^L Rf_!L ⟶ Rf_!(f^{-1}M ⊗^L L)` in the fourth step, read off the map `α` of
[Stacks, Tag 0GL7]: `lowerShriekTensorMap`. It is computed by
`lowerShriekTensorMap_eq`: it is the unit of `f^{-1} ⊣ Rf_*`, followed by the relative cup
product of `f̄` and `Rf̄_*` of the projection isomorphism of `j`, which is the projection map of
[Stacks, Tag 0GL5].

## Main definitions

* `CompactificationData.lowerShriekTensorMap`: the map `M ⊗^L Rf_!L ⟶ Rf_!(f^{-1}M ⊗^L L)`.

## Main results

* `CompactificationData.homEquiv_comp_sheafyTrace`: the string of equalities of the source,
  as an identity of morphisms.
* `CompactificationData.lowerShriekTensorMap_eq`: the projection map through the cup product.
* `CompactificationData.isIso_sheafyTrace_of_isIso_lowerShriekTensorMap`: the map of
  [Stacks, Tag 0GLB] at `(L, K)` is invertible as soon as `lowerShriekTensorMap M L` is for
  every `M`.

## References

* [Stacks Project, Tag 0GLC](https://stacks.math.columbia.edu/tag/0GLC)
* [Stacks Project, Tag 0GLB](https://stacks.math.columbia.edu/tag/0GLB)
* [Stacks Project, Tag 0GL7](https://stacks.math.columbia.edu/tag/0GL7)
* [Stacks Project, Tag 0GL5](https://stacks.math.columbia.edu/tag/0GL5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

/-! ### Two formal identities for a tensor–internal-Hom adjunction -/

/-- The tensor–internal-Hom bijection is precomposition of the evaluation with `h ⊗ 1`. -/
theorem homEquiv_eq_evaluation
    {C : Type*} [Category C] {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} (D : TensorHomAdjunction T H)
    {A B M : C} (h : A ⟶ (H.obj (op B)).obj M) :
    D.homEquiv A B M h = (T.map h).app B ≫ D.toTensorHomBijection.evaluation B M := by
  have e := D.homEquiv_naturality_source h (𝟙 _)
  rw [Category.comp_id] at e
  exact e

/-- The coevaluation `A ⟶ RHom(B, A ⊗ B)` composed with `RHom(B, h)` is the morphism
corresponding to `h : A ⊗ B ⟶ M`. -/
theorem homEquiv_symm_eq_coevaluation
    {C : Type*} [Category C] {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} (D : TensorHomAdjunction T H)
    {A B M : C} (h : (T.obj A).obj B ⟶ M) :
    (D.homEquiv A B M).symm h =
      (D.homEquiv A B ((T.obj A).obj B)).symm (𝟙 _) ≫ (H.obj (op B)).map h := by
  apply (D.homEquiv A B M).injective
  rw [D.homEquiv_naturality_target, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Category.id_comp]

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction

namespace Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {DU : Type u₁} [Category.{v₁} DU] {DX : Type u₂} [Category.{v₂} DX]
  {DY : Type u₃} [Category.{v₃} DY] (data : CompactificationData DU DX DY)
  {upperShriek : DY ⥤ DU} (adj : data.derivedLowerShriek ⊣ upperShriek)
  {pullback : DY ⥤ DU} (pullbackAdj : pullback ⊣ data.derivedPushforward)

/-! ### The projection map read off `α` -/

/-- **The projection map `M ⊗^L Rf_!L ⟶ Rf_!(f^{-1}M ⊗^L L)` read off the map `α` of
[Stacks, Tag 0GL7]**: the morphism corresponding, under the tensor–internal-Hom bijection on
`D(Y_étale, Λ)`, to

`M ⟶ Rf_*f^{-1}M ⟶ Rf_*RHom(L, f^{-1}M ⊗^L L) ⟶ RHom(Rf_!L, Rf_!(f^{-1}M ⊗^L L))`,

the unit of `f^{-1} ⊣ Rf_*`, then `Rf_*` of the coevaluation, then `α`. -/
def lowerShriekTensorMap (M : DY) (L : DU) :
    (data.tensorY.obj M).obj (data.derivedLowerShriek.obj L) ⟶
      data.derivedLowerShriek.obj ((data.tensorU.obj (pullback.obj M)).obj L) :=
  data.adjY.homEquiv _ _ _
    (pullbackAdj.unit.app M ≫
      data.derivedPushforward.map ((data.adjU.homEquiv _ _ _).symm (𝟙 _)) ≫
      data.lowerShriekHomMap L ((data.tensorU.obj (pullback.obj M)).obj L))

/-- **The string of equalities in the proof of [Stacks, Tag 0GLC]**, as an identity of
morphisms: for `g : M ⟶ Rf_*RHom(L, Rf^!K)`, the morphism `M ⊗^L Rf_!L ⟶ K` corresponding to
`g` followed by the map of [Stacks, Tag 0GLB] is the projection map followed by `Rf_!` of the
morphism `f^{-1}M ⊗^L L ⟶ Rf^!K` corresponding to `g` (Tags 07A6 and 08J9) and by the counit of
`Rf_! ⊣ Rf^!`. -/
theorem homEquiv_comp_sheafyTrace (L : DU) (K : DY) (M : DY)
    (g : M ⟶ data.derivedPushforward.obj ((data.homU.obj (op L)).obj (upperShriek.obj K))) :
    data.adjY.homEquiv _ _ _ (g ≫ sheafyTrace data adj L K) =
      lowerShriekTensorMap data pullbackAdj M L ≫
        data.derivedLowerShriek.map (data.adjU.homEquiv _ _ _ ((pullbackAdj.homEquiv _ _).symm g)) ≫
        adj.counit.app K := by
  set h := data.adjU.homEquiv _ _ _ ((pullbackAdj.homEquiv _ _).symm g)
  have hg : g = pullbackAdj.unit.app M ≫
      data.derivedPushforward.map ((data.adjU.homEquiv _ _ _).symm (𝟙 _)) ≫
      data.derivedPushforward.map ((data.homU.obj (op L)).map h) := by
    rw [← Functor.map_comp, ← data.adjU.homEquiv_symm_eq_coevaluation, Equiv.symm_apply_apply]
    exact ((pullbackAdj.homEquiv _ _).apply_symm_apply g).symm.trans
      (pullbackAdj.homEquiv_unit _ _ _)
  have hα : data.derivedPushforward.map ((data.homU.obj (op L)).map h) ≫
        data.lowerShriekHomMap L (upperShriek.obj K) ≫
          (data.homY.obj (op (data.derivedLowerShriek.obj L))).map (adj.counit.app K) =
      data.lowerShriekHomMap L ((data.tensorU.obj (pullback.obj M)).obj L) ≫
        (data.homY.obj (op (data.derivedLowerShriek.obj L))).map
          (data.derivedLowerShriek.map h ≫ adj.counit.app K) := by
    rw [← Category.assoc, data.lowerShriekHomMap_naturality_target, Category.assoc,
      ← Functor.map_comp]
  rw [hg, sheafyTrace_eq, Category.assoc, Category.assoc, hα, ← Category.assoc, ← Category.assoc,
    data.adjY.homEquiv_naturality_target]
  rw [Category.assoc]
  rfl

/-- **The projection map through the cup product**: `lowerShriekTensorMap M L` is the unit of
`f^{-1} ⊣ Rf_*` tensored with `Rf_!L`, followed by the relative cup product of `f̄` at
`(Rj_*f^{-1}M, j_!L)` and by `Rf̄_*` of the projection isomorphism
`Rj_*f^{-1}M ⊗^L j_!L ≅ j_!(f^{-1}M ⊗^L L)`. -/
theorem lowerShriekTensorMap_eq (M : DY) (L : DU) :
    lowerShriekTensorMap data pullbackAdj M L =
      (data.tensorY.map (pullbackAdj.unit.app M)).app _ ≫
        (data.cup.app (data.pushforwardJ.obj (pullback.obj M))).app (data.shriek.obj L) ≫
        data.pushforwardFbar.map ((data.projIso.hom.app (pullback.obj M)).app L) := by
  set c := (data.adjU.homEquiv (pullback.obj M) L _).symm (𝟙 _)
  have hcup := data.cup_naturality_left
    (data.pushforwardJ.map c ≫
      data.openImmersionHomMap L ((data.tensorU.obj (pullback.obj M)).obj L))
    (data.shriek.obj L)
  have hβ : (data.tensorX.map (data.pushforwardJ.map c ≫
        data.openImmersionHomMap L ((data.tensorU.obj (pullback.obj M)).obj L))).app
          (data.shriek.obj L) ≫
        data.adjX.toTensorHomBijection.evaluation (data.shriek.obj L)
          (data.shriek.obj ((data.tensorU.obj (pullback.obj M)).obj L)) =
      (data.projIso.hom.app (pullback.obj M)).app L := by
    rw [← data.adjX.homEquiv_eq_evaluation, data.adjX.homEquiv_naturality_source,
      openImmersionHomMap_homEquiv, ← Category.assoc, data.projIso_naturality_left,
      Category.assoc, ← Functor.map_comp, ← data.adjU.homEquiv_eq_evaluation,
      Equiv.apply_symm_apply]
    simp
  dsimp only [lowerShriekTensorMap, lowerShriekHomMap, Functor.comp_obj, Functor.comp_map]
  rw [← Functor.map_comp_assoc, ← Category.assoc, data.adjY.homEquiv_naturality_source,
    pushforwardHomMap_homEquiv, Functor.map_comp, NatTrans.comp_app, Category.assoc,
    reassoc_of% hcup, ← Functor.map_comp, hβ]

/-- **The map of [Stacks, Tag 0GLB] is invertible once the projection map is**: if
`lowerShriekTensorMap M L : M ⊗^L Rf_!L ⟶ Rf_!(f^{-1}M ⊗^L L)` is an isomorphism for every `M`,
then `Rf_*RHom(L, Rf^!K) ⟶ RHom(Rf_!L, K)` is an isomorphism for every `K`. This is the proof of
[Stacks, Tag 0GLC], the projection formula of [Stacks, Tag 0GL5] being the hypothesis. -/
theorem isIso_sheafyTrace_of_isIso_lowerShriekTensorMap (L : DU)
    (h : ∀ M : DY, IsIso (lowerShriekTensorMap data pullbackAdj M L)) (K : DY) :
    IsIso (sheafyTrace data adj L K) := by
  refine isIso_of_yoneda_map_bijective _ (fun M => ?_)
  have hcomp : (fun g => g ≫ sheafyTrace data adj L K) =
      (data.adjY.homEquiv M _ K).symm ∘
        (fun v => lowerShriekTensorMap data pullbackAdj M L ≫ v) ∘
        (adj.homEquiv _ K).symm ∘
        (data.adjU.homEquiv _ _ _) ∘ (pullbackAdj.homEquiv _ _).symm := by
    funext g
    apply (data.adjY.homEquiv M _ K).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Adjunction.homEquiv_counit]
    exact homEquiv_comp_sheafyTrace data adj pullbackAdj L K M g
  rw [hcomp]
  have := h M
  refine (Equiv.bijective _).comp ((?_ : Function.Bijective _).comp ((Equiv.bijective _).comp
    ((Equiv.bijective _).comp (Equiv.bijective _))))
  exact ⟨fun a b hab => (cancel_epi _).1 hab,
    fun v => ⟨inv (lowerShriekTensorMap data pullbackAdj M L) ≫ v, by simp⟩⟩

/-- **The projection map for a composite adjunction.** When `f^{-1} ⊣ Rf_*` is composed from
adjunctions `f̄^{-1} ⊣ Rf̄_*` and `j^{-1} ⊣ Rj_*`, the projection map
`M ⊗^L Rf_!L ⟶ Rf_!(j^{-1}f̄^{-1}M ⊗^L L)` is invertible as soon as

* the unit of `j^{-1} ⊣ Rj_*` at `f̄^{-1}M`, tensored with `j_!L`, is invertible, and
* the unit of `f̄^{-1} ⊣ Rf̄_*` at `M`, tensored with `Rf̄_*j_!L`, followed by the relative cup
  product of `f̄` at `(f̄^{-1}M, j_!L)`, is invertible. -/
theorem isIso_lowerShriekTensorMap_comp {pullbackFbar : DY ⥤ DX} {pullbackJ : DX ⥤ DU}
    (adjF : pullbackFbar ⊣ data.pushforwardFbar) (adjJ : pullbackJ ⊣ data.pushforwardJ)
    (M : DY) (L : DU)
    (hJ : IsIso ((data.tensorX.map (adjJ.unit.app (pullbackFbar.obj M))).app (data.shriek.obj L)))
    (hF : IsIso ((data.tensorY.map (adjF.unit.app M)).app
        (data.pushforwardFbar.obj (data.shriek.obj L)) ≫
      (data.cup.app (pullbackFbar.obj M)).app (data.shriek.obj L))) :
    IsIso (lowerShriekTensorMap data (adjF.comp adjJ) M L) := by
  rw [lowerShriekTensorMap_eq, ← Category.assoc]
  refine (isIso_comp_right_iff _ _).2 ?_
  rw [Adjunction.comp_unit_app, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [cup_naturality_left, ← Category.assoc]
  infer_instance

end Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData

end
