module

public import StacksFrontier.Deformation.ToposThickening.Helpers.ThickeningTargetPushforward

/-!
# Compatibility of the existence obstructions along a morphism of the targets of two thickenings

Let `i₁ : X ⟶ Y₁` and `i₂ : X ⟶ Y₂` be first order thickenings of one ringed topos and let
`j : Y₂ ⟶ Y₁` be a first order thickening with a map `ρ : i₁_*O_X ⟶ j_*i₂_*O_X` making the square
of structure maps commute (`Deformation.ToposThickening.ThickeningTargetMorphism`), as for a
surjection `A'₁ ⟶ A'₂` of thickenings of `A` and `X_A ⊂ X_{A'₂} ⊂ X_{A'₁}`. Write
`Ψ₀ = ρ^*j_*` for the direct image on modules over the bases and
`θ_F : ℐ₁ ⊗ Ψ₀F ⟶ Ψ₀(ℐ₂ ⊗ F)` for the canonical comparison. Given `c₂ : ℐ₂ ⊗ F ⟶ K₂` on `Y₂`,
`c₁ : ℐ₁ ⊗ Ψ₀F ⟶ K₁` on `Y₁` and `κ : K₁ ⟶ Ψ₀K₂` with `c₁ ≫ κ = θ_F ≫ Ψ₀c₂`, the image under
`Ψ₀` of the obstruction class `o(F, K₂, c₂)` of the second thickening is the obstruction class
`o(Ψ₀F, K₁, c₁)` of the first followed by `κ`. This is Stacks 0CYC for a morphism of thickenings
between different topoi, the situation of Stacks 0CYD, and it is the functoriality of obstruction
classes along surjections used in the proof of Stacks 0CYF.

## Main results

* `Deformation.ToposThickening.ThickeningTargetMorphism.universalClass_pushforward_eq_comp`: a
  map from an extension with a presentation over the first thickening to the direct image of an
  extension with a presentation over the second compares the two universal classes.
* `Deformation.ToposThickening.ThickeningTargetMorphism.baseExtMap_existenceObstructionClass`:
  the comparison of the two obstruction classes.

## Implementation notes

The proof is the one of
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.existenceObstructionClass_first`
with restriction of scalars along `h^♯` replaced by the direct image `j_*`: the direct image of an
extension with injective action map over the second thickening is an extension over the first
whose action map is `θ_F ≫ Ψ₀(d₂)`
(`Deformation.ToposThickening.ThickeningTargetMorphism.pushedExtension_actionMap`), a common
refinement with an extension with injective action map over the first thickening carries a
presentation, and the two defining short exact sequences are related by `(θ_F, γ, c̄)`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0CYC](https://stacks.math.columbia.edu/tag/0CYC)
* [Stacks Project, Tag 0CYD](https://stacks.math.columbia.edu/tag/0CYD)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

universe v u v₁ u₁ v₂ u₂ w e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂}

namespace ThickeningTargetMorphism

variable (D : ThickeningTargetMorphism i₁ i₂) (hi₁ : FirstOrderThickening i₁)
  (hi₂ : FirstOrderThickening i₂) (hj : FirstOrderThickening D.j)

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}] in
include hj in
/-- `Ψ₀ = ρ^*j_*` on modules over the bases is exact: `j_*` is an equivalence for any sheaf of
rings, `j` being a closed immersion of topoi whose direct image is an equivalence, and
restriction of scalars is exact. -/
theorem basePushforward_exact :
    PreservesFiniteLimits D.basePushforward ∧ PreservesFiniteColimits D.basePushforward := by
  have : D.j.toToposHom.pushforward.IsEquivalence := hj.equiv
  have : (pushforwardModuleFunctor D.j.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))).EssSurj :=
    ⟨fun M => Stacks.Sheaves.PushforwardEssentialImage.essSurj_pushforwardModuleFunctor
      D.j.toToposHom _ hj.isClosedImmersion M⟩
  have : (pushforwardModuleFunctor D.j.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))).IsEquivalence := { }
  obtain ⟨_, _⟩ := restrictScalars_exact D.baseHom.structureRingMap
  exact ⟨inferInstanceAs (PreservesFiniteLimits (pushforwardModuleFunctor D.j.toToposHom _ ⋙
      SheafOfModules.restrictScalars D.baseHom.structureRingMap)),
    inferInstanceAs (PreservesFiniteColimits (pushforwardModuleFunctor D.j.toToposHom _ ⋙
      SheafOfModules.restrictScalars D.baseHom.structureRingMap))⟩

/-- **`Ψ₀` on `Ext` groups**, `Ext^n(A, B) ⟶ Ext^n(Ψ₀A, Ψ₀B)`, `Ψ₀` being exact. -/
noncomputable def baseExtMap
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂)))]
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))) (n : ℕ) :
    Abelian.Ext.{e} A B n →+
      Abelian.Ext.{e} (D.basePushforward.obj A) (D.basePushforward.obj B) n :=
  letI := (D.basePushforward_exact hj).1
  letI := (D.basePushforward_exact hj).2
  letI : D.basePushforward.Additive := Functor.additive_of_preserves_binary_products _
  D.basePushforward.mapExtAddHom A B n

variable [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)))]
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂)))]

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- `baseExtMap` sends `x` to its image `x.mapExactFunctor Ψ₀` under the exact functor `Ψ₀`. -/
theorem baseExtMap_apply
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))) (n : ℕ)
    (x : Abelian.Ext.{e} A B n) :
    D.baseExtMap hj A B n x =
      letI := (D.basePushforward_exact hj).1
      letI := (D.basePushforward_exact hj).2
      letI : D.basePushforward.Additive := Functor.additive_of_preserves_binary_products _
      x.mapExactFunctor D.basePushforward := rfl

/-- **A map of extensions across `j` compares the universal classes.** Let `P₂` be a presentation
on an extension `E₂` of `F` over the second thickening and `P` one on an extension `E` of `Ψ₀F`
over the first. If the middle term of `E` maps over `Ψ₀F` to `j_*` of the middle term of `E₂`,
inducing `γ : Q ⟶ Ψ₀Q₂` on kernel modules, then `Ψ₀` of the universal class of `P₂` is the
universal class of `P` pushed forward along `θ_F`. -/
theorem universalClass_pushforward_eq_comp
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O))]
    {F Q₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
    {Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))}
    {E₂ : Abelian.YonedaExtension ((structureRestrict i₂).obj F) ((structureRestrict i₂).obj Q₂) 0}
    {E : Abelian.YonedaExtension ((structureRestrict i₁).obj (D.basePushforward.obj F))
      ((structureRestrict i₁).obj Q) 0}
    (P₂ : MonoActionPresentation hi₂ E₂) (P : MonoActionPresentation hi₁ E)
    (γ : Q ⟶ D.basePushforward.obj Q₂) (u : E.Z.left ⟶ (D.pushedExtension hj E₂).Z.left)
    (hu : E.f ≫ u = (structureRestrict i₁).map γ ≫ (D.pushedExtension hj E₂).f)
    (hg : u ≫ (D.pushedExtension hj E₂).g = E.g) :
    D.baseExtMap hj F _ 2 P₂.universalClass =
      P.universalClass.comp (Abelian.Ext.mk₀ (D.idealTensorMap hi₁ hi₂ F)) (add_zero 2) := by
  have := (D.basePushforward_exact hj).1
  have := (D.basePushforward_exact hj).2
  have : D.basePushforward.Additive := Functor.additive_of_preserves_binary_products _
  have hlim : PreservesFiniteLimits (structureRestrict i₁) :=
    (restrictScalars_exact (structureRingMap i₁)).1
  have hcolim : PreservesFiniteColimits (structureRestrict i₁) :=
    (restrictScalars_exact (structureRingMap i₁)).2
  have hfull : (structureRestrict i₁).Full := hi₁.restrictScalarsFullyFaithful.full
  have hfaith : (structureRestrict i₁).Faithful := hi₁.restrictScalarsFullyFaithful.faithful
  -- the action maps: `d ≫ γ = θ_F ≫ Ψ₀(d₂)`
  have hd : (extensionActionMap hi₁ E).1 ≫ γ =
      D.idealTensorMap hi₁ hi₂ F ≫ D.basePushforward.map (extensionActionMap hi₂ E₂).1 :=
    (extensionActionMap_comp_of_hom hi₁ E (D.pushedExtension hj E₂) γ u hu hg).trans
      (D.pushedExtension_actionMap hi₁ hi₂ hj E₂)
  have hzero : (extensionActionMap hi₁ E).1 ≫ γ ≫ D.basePushforward.map P₂.proj = 0 := by
    rw [← Category.assoc, hd, Category.assoc, ← Functor.map_comp, P₂.zero, Functor.map_zero,
      comp_zero]
  have hepi : Epi P.proj := P.shortExact.epi_g
  obtain ⟨cbar, hbar⟩ := P.shortExact.exact.desc' (γ ≫ D.basePushforward.map P₂.proj) hzero
  -- `Ψ₀` of the defining sequence and of the descent of `P₂`
  have hS₂ := P₂.shortExact.map_of_exact D.basePushforward
  have hD₂ : (ShortComplex.mk (D.basePushforward.map P₂.descent.f)
      (D.basePushforward.map P₂.descent.g) (by
        rw [← Functor.map_comp, yonedaExtension_comp_zero, Functor.map_zero])).ShortExact :=
    (yonedaExtension_shortExact P₂.descent).map_of_exact D.basePushforward
  let D₂ := Abelian.shortExactYonedaExtension hD₂
  -- the comparison exhibiting the restriction of `Ψ₀` of the descent as a pushout of `E`
  obtain ⟨hw₁, hw₂⟩ := D.pushedExtension_comparison hj E₂ P₂.proj P₂.descent P₂.comparison
    P₂.comparison_left P₂.comparison_right
  have hcmp₁ : E.f ≫ (u ≫ (D.j.pushforwardModules.map P₂.comparison ≫
        (D.restrictIso P₂.descent.Z.left).hom)) =
      (structureRestrict i₁).map (γ ≫ D.basePushforward.map P₂.proj) ≫
        (structureRestrict i₁).map (D.basePushforward.map P₂.descent.f) := by
    rw [Functor.map_comp, Category.assoc, ← hw₁, ← Category.assoc, hu, Category.assoc]
  have hcmp₂ : (u ≫ (D.j.pushforwardModules.map P₂.comparison ≫
        (D.restrictIso P₂.descent.Z.left).hom)) ≫
      (structureRestrict i₁).map (D.basePushforward.map P₂.descent.g) = E.g :=
    (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) hw₂).trans hg)
  have hξ : (yonedaExtension_shortExact D₂).extClass =
      (yonedaExtension_shortExact P.descent).extClass.comp (Abelian.Ext.mk₀ cbar) (add_zero 1) := by
    apply (structureRestrict i₁).extMap_injective_of_fullyFaithful (D.basePushforward.obj F)
      (D.basePushforward.obj P₂.C)
    rw [Functor.mapExtAddHom_comp_mk₀,
      mapExtAddHom_descent_extClass (γ ≫ D.basePushforward.map P₂.proj) D₂ _ hcmp₁ hcmp₂,
      mapExtAddHom_descent_extClass P.proj P.descent P.comparison P.comparison_left
        P.comparison_right,
      Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
    exact congrArg (fun φ => (extensionClass _ _ E).comp (Abelian.Ext.mk₀ φ) (add_zero 1))
      ((congrArg (structureRestrict i₁).map hbar.symm).trans (Functor.map_comp _ _ _))
  rw [baseExtMap_apply, MonoActionPresentation.universalClass, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_extClass, Abelian.Ext.mapExactFunctor_extClass]
  exact Abelian.comp_extClass_naturality hS₂ P.shortExact
    (⟨D.idealTensorMap hi₁ hi₂ F, γ, cbar, hd.symm, hbar.symm⟩ :
      ShortComplex.mk (extensionActionMap hi₁ E).1 P.proj P.zero ⟶
        (ShortComplex.mk (extensionActionMap hi₂ E₂).1 P₂.proj P₂.zero).map D.basePushforward)
    (yonedaExtension_shortExact D₂).extClass (yonedaExtension_shortExact P.descent).extClass hξ

/-- **The obstruction classes of two thickenings related by a morphism of their targets are
compatible** (Stacks 0CYC, across the morphism `j : Y₂ ⟶ Y₁` of Stacks 0CYD): for
`c₂ : ℐ₂ ⊗ F ⟶ K₂`, `c₁ : ℐ₁ ⊗ Ψ₀F ⟶ K₁` and `κ : K₁ ⟶ Ψ₀K₂` with `c₁ ≫ κ = θ_F ≫ Ψ₀c₂`,
`Ψ₀` carries the obstruction class `o(F, K₂, c₂)` of the second thickening to the obstruction
class `o(Ψ₀F, K₁, c₁)` of the first pushed forward along `κ`. For a surjection `A'₁ ⟶ A'₂` of
thickenings of `A`, with `Y₂ = X_{A'₂} ⊂ Y₁ = X_{A'₁}`, this is the functoriality of obstruction
classes along surjections of Stacks 0CYF: the class over `A'₂` is the image of the class over
`A'₁`. -/
theorem baseExtMap_existenceObstructionClass
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O))]
    (F K₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂)))
    (K₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)))
    (c₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).obj hi₂.I).obj F ⟶ K₂)
    (c₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).obj
      (D.basePushforward.obj F) ⟶ K₁)
    (κ : K₁ ⟶ D.basePushforward.obj K₂)
    (hκ : c₁ ≫ κ = D.idealTensorMap hi₁ hi₂ F ≫ D.basePushforward.map c₂) :
    D.baseExtMap hj F K₂ 2 (existenceObstructionClass hi₂ F K₂ c₂) =
      (existenceObstructionClass hi₁ (D.basePushforward.obj F) K₁ c₁).comp
        (Abelian.Ext.mk₀ κ) (add_zero 2) := by
  classical
  have := (D.basePushforward_exact hj).1
  have := (D.basePushforward_exact hj).2
  have : D.basePushforward.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨Q₂, E₂, ⟨P₂⟩⟩ := exists_extension_monoActionPresentation hi₂ F
  obtain ⟨Q₁, E₁, ⟨P₁⟩⟩ := exists_extension_monoActionPresentation hi₁ (D.basePushforward.obj F)
  obtain ⟨E₃, u₁, u₂, ⟨hu₁, hg₁⟩, hu₂, hg₂⟩ :=
    exists_extension_hom_pair_of_extensions E₁ (D.pushedExtension hj E₂)
  have hd₁ : (extensionActionMap hi₁ E₃).1 ≫ biprod.fst = (extensionActionMap hi₁ E₁).1 :=
    extensionActionMap_comp_of_hom hi₁ E₃ E₁ biprod.fst u₁ hu₁ hg₁
  have : Mono (extensionActionMap hi₁ E₁).1 := P₁.shortExact.mono_f
  obtain ⟨P₃⟩ := exists_monoActionPresentation hi₁ E₃ (mono_of_mono_fac hd₁)
  have huniv := D.universalClass_pushforward_eq_comp hi₁ hi₂ hj P₂ P₃ biprod.snd u₂ hu₂ hg₂
  rw [existenceObstructionClass_eq_obstruction hi₁ (D.basePushforward.obj F) K₁ c₁ P₃,
    existenceObstructionClass_eq_obstruction hi₂ F K₂ c₂ P₂]
  show D.baseExtMap hj F K₂ 2 (P₂.universalClass.comp (Abelian.Ext.mk₀ c₂) (add_zero 2)) =
    (P₃.universalClass.comp (Abelian.Ext.mk₀ c₁) (add_zero 2)).comp
      (Abelian.Ext.mk₀ κ) (add_zero 2)
  rw [baseExtMap_apply, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    ← baseExtMap_apply, huniv, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_comp_mk₀, hκ]

end ThickeningTargetMorphism

end Deformation.ToposThickening

end
