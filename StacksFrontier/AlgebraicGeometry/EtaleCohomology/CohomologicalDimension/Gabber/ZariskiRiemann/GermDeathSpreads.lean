module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenteredGermDeathOfValuation

/-!
# A dying germ dies on a neighbourhood

Let `π : Y' ⟶ Y` be a refinement of proper models, `U ⟶ Y` étale and `g` a section of
`G = R^q j_* F` over `U`. This file proves
`AlgebraicGeometry.Scheme.ZariskiRiemann.GermDeathSpreads`: if the germ of `g` dies at a
geometric point `(s, ℓ)` of `U ×_Y Y'`, the point of `U ×_Y Y'` it defines lies in the dead set
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.deadSet`.

The argument:

1. Let `g'` be the section of `G' = R^q j'_* F` over `U ×_Y Y'` obtained by pulling `g` back
   along `π` (the unit of the inverse-image/direct-image adjunction) and applying the base change
   map `π⁻¹ G ⟶ G'`
   (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.baseChangeSection`). The
   transition map of stalks at `s` sends the germ of `g` at `ℓ` to the germ of `g'` at the lift
   `(ℓ, s)` of `s` to `U ×_Y Y'` (`Refinement.stalkTransition_toPresheafFiber`), by the
   description of the stalk of an inverse image on germs,
   `Stacks.EtaleCohomology.toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv`.
2. A germ which vanishes vanishes near its point
   (`Stacks.EtaleCohomology.exists_isOpen_forall_toPresheafFiber_eq_zero`): it vanishes on an étale neighbourhood `E`, the image of `E` is
   open (étale morphisms are open) and every geometric point in it lifts to `E`
   (`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`).

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.baseChangeSection`

## Main results

* `Stacks.EtaleCohomology.exists_isOpen_forall_toPresheafFiber_eq_zero` — a germ which vanishes
  vanishes at every geometric point of an open neighbourhood.
* `Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso_inv_map_toPresheafFiber`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition_toPresheafFiber`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.deadAt_iff_toPresheafFiber`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.germDeathSpreads`

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

private instance forgetAddCommGrpCatPreservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u, u}
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u}
    (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- **A germ which vanishes vanishes near its point.** Let `H` be an abelian sheaf on `X_étale`,
`U ⟶ X` étale, `z ∈ H(U)` and `ū` a lift to `U` of a geometric point of `X` with `z_ū = 0`.
Then there is an open `O ⊆ U` containing the point of `ū` such that `z_{ū₁} = 0` for every lift
`ū₁` to `U` of a geometric point of `X` lying at a point of `O`.

`z` vanishes on an étale neighbourhood `h : E ⟶ U` of `ū`; take `O = h(E)`, open as `h` is étale;
a geometric point of `U` at a point of `O` lifts to `E`
(`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`). -/
theorem exists_isOpen_forall_toPresheafFiber_eq_zero {X : Scheme.{u}}
    (H : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (U : X.Etale) (z : H.obj.obj (op U))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (ū : (Scheme.pointSmallEtale x).fiber.obj U)
    (hz : (Scheme.pointSmallEtale x).toPresheafFiber U ū H.obj z = 0) :
    ∃ O : Set ↥U.left, IsOpen O ∧ ū.left (default : Spec (.of Ω)) ∈ O ∧
      ∀ (Ω₁ : Type u) [Field Ω₁] [IsSepClosed Ω₁] (x₁ : Spec (.of Ω₁) ⟶ X)
        (ū₁ : (Scheme.pointSmallEtale x₁).fiber.obj U), ū₁.left (default : Spec (.of Ω₁)) ∈ O →
        (Scheme.pointSmallEtale x₁).toPresheafFiber U ū₁ H.obj z = 0 := by
  obtain ⟨V, f, y, hy, hf⟩ := ((Scheme.pointSmallEtale x).toPresheafFiber_eq_iff' U ū z 0).1
    (hz.trans (map_zero _).symm)
  rw [map_zero] at hf
  have : Etale f.left := inferInstance
  have : Flat f.left := inferInstance
  have : LocallyOfFinitePresentation f.left := inferInstance
  have : UniversallyOpen f.left := UniversallyOpen.of_flat f.left
  refine ⟨Set.range f.left, f.left.isOpenMap.isOpen_range,
    ⟨y.left (default : Spec (.of Ω)), ?_⟩, ?_⟩
  · rw [← hy]
    rfl
  · intro Ω₁ _ _ x₁ ū₁ ⟨v, hv⟩
    obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed f.left ū₁.left v hv
    let y₁ : (Scheme.pointSmallEtale x₁).fiber.obj V := Over.homMk l (by
      change l ≫ V.hom = x₁
      rw [← MorphismProperty.Over.w f, ← Category.assoc, hl]
      exact Over.w ū₁)
    have hy₁ : (Scheme.pointSmallEtale x₁).fiber.map f y₁ = ū₁ := Over.OverMorphism.ext hl
    rw [← hy₁, ← Point.toPresheafFiber_w_apply, hf, map_zero]

/-- **The stalk comparison of an inverse image, followed by a stalk map, on germs.** For
`π : X' ⟶ X`, a geometric point `s` of `X'`, an abelian étale sheaf `G` on `X` and a morphism
`β : π⁻¹ G ⟶ G'`, the germ of a section `g` of `G` at a lift `ℓ` of `s ≫ π` to `W` goes to the
germ of `β (π^* g)` at the corresponding lift of `s` to `W ×_X X'`. -/
theorem smallEtaleStalkPullbackAbIso_inv_map_toPresheafFiber {X X' : Scheme.{u}} (π : X' ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X')
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) {G' : Sheaf (smallEtaleTopology X') Ab.{u + 1}}
    (β : (smallEtalePullbackAb π).obj G ⟶ G') (W : X.Etale)
    (ℓ : (Scheme.pointSmallEtale (s ≫ π)).fiber.obj W) (g : G.obj.obj (op W)) :
    (((smallEtaleStalkPullbackAbIso π s).app G).inv ≫ (smallEtaleStalkAb s).map β)
        ((Scheme.pointSmallEtale (s ≫ π)).toPresheafFiber W ℓ G.obj g) =
      (Scheme.pointSmallEtale s).toPresheafFiber ((smallEtaleBaseChange π).obj W)
        ((pointSmallEtaleComapFiberIso π s).hom.app W ℓ) G'.obj
        (β.hom.app _ (((smallEtaleAdjunctionAb π).unit.app G).hom.app (op W) g)) := by
  have h : ((smallEtaleStalkPullbackAbIso π s).inv.app G)
      ((Scheme.pointSmallEtale (s ≫ π)).toPresheafFiber W ℓ G.obj g) =
      (Scheme.pointSmallEtale s).toPresheafFiber ((smallEtaleBaseChange π).obj W)
        ((pointSmallEtaleComapFiberIso π s).hom.app W ℓ) ((smallEtalePullbackAb π).obj G).obj
        (((smallEtaleAdjunctionAb π).unit.app G).hom.app (op W) g) :=
    ConcreteCategory.congr_hom (toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv π s G W ℓ) g
  change (Scheme.pointSmallEtale s).presheafFiber.map β.hom
    (((smallEtaleStalkPullbackAbIso π s).inv.app G)
      ((Scheme.pointSmallEtale (s ≫ π)).toPresheafFiber W ℓ G.obj g)) = _
  rw [h]
  exact Point.toPresheafFiber_naturality_apply (Scheme.pointSmallEtale s) _ _ _ _

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

namespace ProperModel

variable {B : Type u} [CommRing B]

/-- **The pulled-back section.** For a refinement `π : Y' ⟶ Y`, an étale `U ⟶ Y` and a section
`g` of `R^q j_* F` over `U`, the section of `R^q j'_* F` over `U ×_Y Y'`: the image of `g` under
the unit of the inverse-image/direct-image adjunction along `π`, followed by the base change map
`π⁻¹ R^q j_* F ⟶ R^q j'_* F`. -/
def Refinement.baseChangeSection {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U)) :
    (((etaleAbelianDirectImage.{u, 0} M'.j).rightDerived q).obj
        ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F)).obj.obj
      (op ((Stacks.EtaleCohomology.smallEtaleBaseChange φ.π).obj U)) :=
  ((smallEtalePullbackAbIsoEtaleAbelianInverseImage φ.π).hom.app _ ≫
      etaleAbelianInverseImageRightDerivedDirectImageBaseChange M.j φ.π (𝟙 _) M'.j
        (by rw [Category.id_comp, φ.fac]) F q).hom.app _
    (((smallEtaleAdjunctionAb φ.π).unit.app
      (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)).hom.app (op U) g)

/-- **The transition map on germs.** The transition map of stalks along a refinement `π` at a
geometric point `s` of `Y'` sends the germ of `g` at a lift `ℓ` of `s ≫ π` to `U` to the germ of
the pulled-back section at the corresponding lift of `s` to `U ×_Y Y'`. -/
theorem Refinement.stalkTransition_toPresheafFiber {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
    (ℓ : (Scheme.pointSmallEtale (s ≫ φ.π)).fiber.obj U) :
    φ.stalkTransition F q s ((Scheme.pointSmallEtale (s ≫ φ.π)).toPresheafFiber U ℓ
        (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj g) =
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Stacks.EtaleCohomology.smallEtaleBaseChange φ.π).obj U)
        ((pointSmallEtaleComapFiberIso φ.π s).hom.app U ℓ)
        (((etaleAbelianDirectImage.{u, 0} M'.j).rightDerived q).obj
          ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F)).obj
        (φ.baseChangeSection F q U g) :=
  smallEtaleStalkPullbackAbIso_inv_map_toPresheafFiber φ.π s _ _ U ℓ g

/-- **Death of a germ is vanishing of the germ of the pulled-back section.** -/
theorem Refinement.deadAt_iff_toPresheafFiber {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
    (ℓ : (Scheme.pointSmallEtale (s ≫ φ.π)).fiber.obj U) :
    φ.DeadAt F q U g s rfl ℓ ↔
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Stacks.EtaleCohomology.smallEtaleBaseChange φ.π).obj U)
        ((pointSmallEtaleComapFiberIso φ.π s).hom.app U ℓ)
        (((etaleAbelianDirectImage.{u, 0} M'.j).rightDerived q).obj
          ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F)).obj
        (φ.baseChangeSection F q U g) = 0 := by
  rw [Refinement.DeadAt, eqToHom_refl, Category.id_comp, stalkTransition_toPresheafFiber]
  exact Iff.rfl

/-- The point of `U ×_Y Y'` of a geometric point `s` of `Y'` and a lift `ℓ` of `s ≫ π` to `U` is
the image of the closed point under the corresponding lift of `s` to `U ×_Y Y'`. -/
theorem Refinement.germPoint_eq {M' M : ProperModel B} (φ : Refinement M' M) (U : M.Y.Etale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
    (ℓ : (Scheme.pointSmallEtale (s ≫ φ.π)).fiber.obj U) :
    φ.germPoint U s rfl ℓ =
      ((pointSmallEtaleComapFiberIso φ.π s).hom.app U ℓ).left (default : Spec (.of Ω)) := by
  have h : pullback.lift (etaleLiftHom ℓ) s (etaleLiftHom_comp ℓ) =
      ((pointSmallEtaleComapFiberIso φ.π s).hom.app U ℓ).left := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp only [pointSmallEtaleComapFiberIso, pointSmallEtaleBaseChangeFiberIso,
        Over.mapPullbackAdj, NatIso.ofComponents_hom_app, Adjunction.mkOfHomEquiv_homEquiv]
      exact (pullback.lift_fst _ _ _).symm
    · rw [pullback.lift_snd]
      exact (Over.w ((pointSmallEtaleComapFiberIso φ.π s).hom.app U ℓ)).symm
  rw [Refinement.germPoint, h]
  rfl

end ProperModel

/-- **A dying germ dies on a neighbourhood** (for the
pulled-back section on `U ×_Y Y'`). If the germ of `g` dies at a geometric point
`(s, ℓ)` of `U ×_Y Y'`, the point of `U ×_Y Y'` it defines lies in the dead set: the germ of the
pulled-back section vanishes on an étale neighbourhood, whose image is an open neighbourhood all
of whose geometric points lift to it. -/
theorem germDeathSpreads : GermDeathSpreads.{u} := by
  intro B _ _ M' M φ F q U g Ω _ _ s t ht ℓ hd
  subst ht
  rw [ProperModel.Refinement.deadAt_iff_toPresheafFiber] at hd
  obtain ⟨O, hO, hmem, hall⟩ := exists_isOpen_forall_toPresheafFiber_eq_zero _ _ _ s _ hd
  refine ⟨O, hO, by rwa [ProperModel.Refinement.germPoint_eq], ?_⟩
  intro Ω' _ _ s' t' ht' ℓ' hmem'
  subst ht'
  rw [ProperModel.Refinement.germPoint_eq] at hmem'
  rw [ProperModel.Refinement.deadAt_iff_toPresheafFiber]
  exact hall Ω' s' _ hmem'

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
