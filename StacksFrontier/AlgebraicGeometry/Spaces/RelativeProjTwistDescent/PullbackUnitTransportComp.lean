module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedSquareRightAdjointCompat
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.PushforwardTerminalSectionsComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ZariskiPullbackTensor

/-!
# Stacks 03LU read through identifications of pullbacks: composition and squares

Let `φ : X ⟶ Y`, `ψ : Y ⟶ Z` and `χ : X ⟶ Z` be morphisms of ringed topoi, `χ` a composite of
`φ` and `ψ` in the sense of a comparison `τ` of geometric direct images carrying the composite
structure map to that of `χ`.  The identification `f^*𝒪 ≅ 𝒪` of Stacks 03LU
(`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`) is compatible with the
comparison `χ^* ≅ ψ^* ⋙ φ^*` of pullbacks.  Both are read off universal properties: a morphism out
of `f^*𝒪` is a global section, through the adjunction of Stacks 03D7, and the comparison of
pullbacks is the one whose transpose is the unit of the composite adjunction.  So the composition
law comes down to the composition law of the identification of global sections along a composite
of geometric morphisms, `MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans`.

As for Stacks 03EL (`Stacks.SheafOfModules.pullbackTensorIsoTransport_square`), the law is then
read through identifications `α` of functors with the pullbacks, along a composite and round a
square of two factorizations, and at the square of a morphism of representable algebraic spaces.
This is the unit companion of
`AlgebraicGeometry.Space.representedSquare_pullbackTensorIsoTransport_mateEquiv`.

## Main results

* `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_hom_comp_pullbackModulesCompIso`:
  **Stacks 03LU composes along the comparison of pullbacks.**
* `Stacks.SheafOfModules.pullbackUnitIsoTransport_comp`: the transported identifications compose
  along an identification corresponding to the comparison of pullbacks.
* `Stacks.SheafOfModules.pullbackUnitIsoTransport_square`: the transported identifications are
  compatible with an isomorphism between two factorizations.
* `Stacks.SheafOfModules.pullbackUnitIsoTransport_square_factorizationPullbackIso_of_hom_eq`: the
  same through `Stacks.SheafOfModules.factorizationPullbackIso`.
* `AlgebraicGeometry.Space.representedSquare_pullbackUnitIsoTransport_mateEquiv`: **Stacks 03LU
  round the square of a morphism of the site**, with the comparison of the two factorizations
  written as the inverse mate of `AlgebraicGeometry.Space.representedModulePullbackIso`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedToposModules

universe w w' w'' v u v' u' v'' u''

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
    {Z : AlgebraicGeometry.RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) (χ : RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The transpose of the comparison of pullbacks at a sheaf of modules `G` is the unit of the
composite adjunction followed by the comparison of direct images. -/
private theorem homEquiv_pullbackModulesCompIso_hom_app
    (G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (pullbackAdjPushforwardModules χ).homEquiv _ _
        ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G) =
      (pullbackAdjPushforwardModules ψ).homEquiv _ _
          ((pullbackAdjPushforwardModules φ).unit.app (ψ.pullbackModules.obj G)) ≫
        (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app
          (φ.pullbackModules.obj (ψ.pullbackModules.obj G)) := by
  have h := unit_pullbackModulesCompIso_hom_app φ ψ χ τ hτ G
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id] at h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← Adjunction.comp_unit_app, ← h]
  have hnat := (pushforwardModulesCompIso φ ψ χ τ hτ).hom.naturality
    ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app G)
  simp only [Iso.symm_hom, Category.assoc]
  exact congrArg _ ((Iso.inv_comp_eq ((pushforwardModulesCompIso φ ψ χ τ hτ).app _)).2 hnat).symm

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **Stacks 03LU composes along the comparison of pullbacks**: the identification
`𝒪_X ≅ χ^*𝒪_Z` followed by the comparison `χ^* ≅ ψ^* ⋙ φ^*` at `𝒪_Z` is the identification
`𝒪_X ≅ φ^*𝒪_Y` followed by `φ^*` of the identification `𝒪_Y ≅ ψ^*𝒪_Z`. -/
theorem pullbackModulesObjUnitIso_hom_comp_pullbackModulesCompIso :
    (pullbackModulesObjUnitIso χ).hom ≫ (pullbackModulesCompIso φ ψ χ τ hτ).hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) =
      (pullbackModulesObjUnitIso φ).hom ≫
        φ.pullbackModules.map (pullbackModulesObjUnitIso ψ).hom := by
  rw [pullbackModulesObjUnitIso_hom_comp, pullbackModulesObjUnitIso_hom_comp]
  refine congrArg (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) _).symm ?_
  have hY : unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _
      ((pullbackModulesObjUnitIso ψ).hom ≫ (pullbackAdjPushforwardModules φ).unit.app
        (ψ.pullbackModules.obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))) =
      pushforwardModulesUnitHomEquiv ψ _ ((pullbackAdjPushforwardModules ψ).homEquiv _ _
        ((pullbackAdjPushforwardModules φ).unit.app (ψ.pullbackModules.obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))))) := by
    rw [pullbackModulesObjUnitIso_hom_comp]
    exact Equiv.apply_symm_apply _ _
  have hR : (pullbackAdjPushforwardModules φ).homEquiv _ _
      (φ.pullbackModules.map (pullbackModulesObjUnitIso ψ).hom) =
      (pullbackModulesObjUnitIso ψ).hom ≫ (pullbackAdjPushforwardModules φ).unit.app
        (ψ.pullbackModules.obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) := by
    rw [Adjunction.homEquiv_unit]
    exact ((pullbackAdjPushforwardModules φ).unit.naturality _).symm
  refine (congrArg (pushforwardModulesUnitHomEquiv χ _)
    (homEquiv_pullbackModulesCompIso_hom_app φ ψ χ τ hτ _)).trans ?_
  refine Eq.trans ?_ (congrArg (pushforwardModulesUnitHomEquiv φ _) hR).symm
  refine Eq.trans ?_ (congrArg (φ.toToposHom.pushforwardTerminalHomEquiv _) hY).symm
  refine Eq.trans (congrArg (χ.toToposHom.pushforwardTerminalHomEquiv _)
    (unitTerminalHomEquiv_comp _ _ _)) ?_
  exact MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans φ.toToposHom ψ.toToposHom
    χ.toToposHom τ.hom _ _

end Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section Comp

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
    {Z : AlgebraicGeometry.RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) (χ : RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
    τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  {Lφ : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  {Lψ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)}
  {Lχ : _root_.SheafOfModules.{w''} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  (αφ : φ.pullbackModules ≅ Lφ) (αψ : ψ.pullbackModules ≅ Lψ) (αχ : χ.pullbackModules ≅ Lχ)

omit [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- **The transported identifications of Stacks 03LU compose.**  Let `β : L_χ ≅ L_ψ ⋙ L_φ`
correspond to the comparison `χ^* ≅ ψ^* ⋙ φ^*` of pullbacks under the identifications
`α_φ, α_ψ, α_χ`.  Then the identification `L_χ 𝒪 ≅ 𝒪` is `β` at `𝒪`, followed by `L_φ` of the
identification for `L_ψ` and by the identification for `L_φ`.

This is
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_hom_comp_pullbackModulesCompIso`
read through the identifications; it is the unit companion of
`Stacks.SheafOfModules.pullbackTensorIsoTransport_comp`. -/
theorem pullbackUnitIsoTransport_comp (β : Lχ ≅ Lψ ⋙ Lφ)
    (hβ : ∀ M, (pullbackModulesCompIso φ ψ χ τ hτ).hom.app M ≫
        φ.pullbackModules.map (αψ.hom.app M) ≫ αφ.hom.app (Lψ.obj M) =
      αχ.hom.app M ≫ β.hom.app M) :
    (pullbackUnitIsoTransport χ αχ).hom =
      β.hom.app (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O)) ≫
        Lφ.map (pullbackUnitIsoTransport ψ αψ).hom ≫ (pullbackUnitIsoTransport φ αφ).hom := by
  have hb : β.hom.app (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O)) =
      αχ.inv.app _ ≫ (pullbackModulesCompIso φ ψ χ τ hτ).hom.app _ ≫
        φ.pullbackModules.map (αψ.hom.app _) ≫ αφ.hom.app _ :=
    (Iso.eq_inv_comp (αχ.app _)).2 (hβ _).symm
  have hlaw' : (pullbackModulesCompIso φ ψ χ τ hτ).hom.app
        (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O)) ≫
        φ.pullbackModules.map (pullbackModulesObjUnitIso ψ).inv ≫
          (pullbackModulesObjUnitIso φ).inv = (pullbackModulesObjUnitIso χ).inv := by
    rw [← cancel_epi (pullbackModulesObjUnitIso χ).hom,
      reassoc_of% (pullbackModulesObjUnitIso_hom_comp_pullbackModulesCompIso φ ψ χ τ hτ),
      Iso.hom_inv_id, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id]
  have hΦ : ∀ {M M' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (k : M ⟶ M'),
      αφ.hom.app M ≫ Lφ.map k ≫ αφ.inv.app M' = φ.pullbackModules.map k := fun k => by
    rw [← αφ.hom.naturality_assoc k, Iso.hom_inv_id_app, Category.comp_id]
  simp only [pullbackUnitIsoTransport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [hb]
  simp only [Category.assoc]
  refine congrArg (fun t => αχ.inv.app _ ≫ t) ?_
  rw [← hlaw']
  refine congrArg (fun t => (pullbackModulesCompIso φ ψ χ τ hτ).hom.app _ ≫ t) ?_
  rw [reassoc_of% (hΦ _), ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]

end Comp

section Square

universe wX vX uX wZ vZ uZ wA vA uA wB vB uB

variable {X : AlgebraicGeometry.RingedTopos.{vX, uX, wX}}
    {Z : AlgebraicGeometry.RingedTopos.{vZ, uZ, wZ}}
    {Y₁ : AlgebraicGeometry.RingedTopos.{vA, uA, wA}}
    {Y₂ : AlgebraicGeometry.RingedTopos.{vB, uB, wB}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wX} RingCat.{wX})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{wZ} RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [X.J.HasSheafCompose (forget RingCat.{wX})] [Z.J.HasSheafCompose (forget RingCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget RingCat.{wA})] [Y₂.J.HasSheafCompose (forget RingCat.{wB})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wX})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{wZ})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{wA})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [HasWeakSheafify X.J AddCommGrpCat.{wX}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wX}]
  [HasWeakSheafify Z.J AddCommGrpCat.{wZ}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{wZ}]
  [HasWeakSheafify Y₁.J AddCommGrpCat.{wA}] [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{wA}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{wB}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  (φ₁ : RingedToposHom X Y₁) (ψ₁ : RingedToposHom Y₁ Z)
  (φ₂ : RingedToposHom X Y₂) (ψ₂ : RingedToposHom Y₂ Z) (χ : RingedToposHom X Z)
  (τ₁ : φ₁.toToposHom.pushforward ⋙ ψ₁.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₁ : fSharpSetComp φ₁ ψ₁ ≫
    τ₁.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  (τ₂ : φ₂.toToposHom.pushforward ⋙ ψ₂.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ₂ : fSharpSetComp φ₂ ψ₂ ≫
    τ₂.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)
  {Lφ₁ : _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O) ⥤
    _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
  {Lψ₁ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wA} (Tensor.ringSheaf Y₁.O)}
  {Lφ₂ : _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O) ⥤
    _root_.SheafOfModules.{wX} (Tensor.ringSheaf X.O)}
  {Lψ₂ : _root_.SheafOfModules.{wZ} (Tensor.ringSheaf Z.O) ⥤
    _root_.SheafOfModules.{wB} (Tensor.ringSheaf Y₂.O)}
  (αφ₁ : φ₁.pullbackModules ≅ Lφ₁) (αψ₁ : ψ₁.pullbackModules ≅ Lψ₁)
  (αφ₂ : φ₂.pullbackModules ≅ Lφ₂) (αψ₂ : ψ₂.pullbackModules ≅ Lψ₂)

omit [HasWeakSheafify Z.J AddCommGrpCat.{wZ}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{wZ}] in
/-- **The transported identifications of Stacks 03LU are compatible with an isomorphism between
two factorizations.**  Let `χ` factor through `φ₁, ψ₁` and through `φ₂, ψ₂`, and let
`m : L_ψ₁ ⋙ L_φ₁ ≅ L_ψ₂ ⋙ L_φ₂` correspond to the two comparisons of pullbacks under the
identifications `α`.  Then the identification `L_φ₁ L_ψ₁ 𝒪 ≅ 𝒪` through `L_ψ₁, L_φ₁` is `m` at
`𝒪` followed by the identification through `L_ψ₂, L_φ₂`.  It is the unit companion of
`Stacks.SheafOfModules.pullbackTensorIsoTransport_square`. -/
theorem pullbackUnitIsoTransport_square (m : Lψ₁ ⋙ Lφ₁ ≅ Lψ₂ ⋙ Lφ₂)
    (hm : ∀ M, (pullbackModulesCompIso φ₁ ψ₁ χ τ₁ hτ₁).hom.app M ≫
        φ₁.pullbackModules.map (αψ₁.hom.app M) ≫ αφ₁.hom.app (Lψ₁.obj M) ≫ m.hom.app M =
      (pullbackModulesCompIso φ₂ ψ₂ χ τ₂ hτ₂).hom.app M ≫
        φ₂.pullbackModules.map (αψ₂.hom.app M) ≫ αφ₂.hom.app (Lψ₂.obj M)) :
    Lφ₁.map (pullbackUnitIsoTransport ψ₁ αψ₁).hom ≫ (pullbackUnitIsoTransport φ₁ αφ₁).hom =
      m.hom.app (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O)) ≫
        Lφ₂.map (pullbackUnitIsoTransport ψ₂ αψ₂).hom ≫ (pullbackUnitIsoTransport φ₂ αφ₂).hom := by
  let T₁ : χ.pullbackModules ≅ Lψ₁ ⋙ Lφ₁ := pullbackModulesCompIso φ₁ ψ₁ χ τ₁ hτ₁ ≪≫
    Functor.isoWhiskerRight αψ₁ φ₁.pullbackModules ≪≫ Functor.isoWhiskerLeft Lψ₁ αφ₁
  have hT₁ : ∀ M, T₁.hom.app M = (pullbackModulesCompIso φ₁ ψ₁ χ τ₁ hτ₁).hom.app M ≫
      φ₁.pullbackModules.map (αψ₁.hom.app M) ≫ αφ₁.hom.app (Lψ₁.obj M) := fun _ => rfl
  have h₁ := pullbackUnitIsoTransport_comp φ₁ ψ₁ χ τ₁ hτ₁ αφ₁ αψ₁ (Iso.refl _) T₁
    (fun M => (hT₁ M).symm.trans (Category.id_comp _).symm)
  have h₂ := pullbackUnitIsoTransport_comp φ₂ ψ₂ χ τ₂ hτ₂ αφ₂ αψ₂ (Iso.refl _) (T₁ ≪≫ m)
    (fun M => (hm M).symm.trans (by
      rw [Iso.trans_hom, NatTrans.comp_app, hT₁, Iso.refl_hom, NatTrans.id_app,
        Category.id_comp]
      simp only [Category.assoc]))
  rw [h₁, Iso.trans_hom, NatTrans.comp_app, Category.assoc] at h₂
  exact ((T₁.app _).cancel_iso_hom_left _ _).1 h₂

omit [HasWeakSheafify Z.J AddCommGrpCat.{wZ}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{wZ}] in
/-- `Stacks.SheafOfModules.pullbackUnitIsoTransport_square` at
`Stacks.SheafOfModules.factorizationPullbackIso`, with the comparison of the factorizations
replaced by a natural transformation `θ` it is equal to.  It is the unit companion of
`Stacks.SheafOfModules.pullbackTensorIsoTransport_square_factorizationPullbackIso_of_hom_eq`. -/
theorem pullbackUnitIsoTransport_square_factorizationPullbackIso_of_hom_eq
    (θ : Lψ₁ ⋙ Lφ₁ ⟶ Lψ₂ ⋙ φ₂.pullbackModules)
    (hθ : (factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂).hom = θ) :
    Lφ₁.map (pullbackUnitIsoTransport ψ₁ αψ₁).hom ≫ (pullbackUnitIsoTransport φ₁ αφ₁).hom =
      θ.app (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O)) ≫
        φ₂.pullbackModules.map (pullbackUnitIsoTransport ψ₂ αψ₂).hom ≫
          (pullbackUnitIsoTransport φ₂ (Iso.refl _)).hom := by
  subst hθ
  refine pullbackUnitIsoTransport_square φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ (Iso.refl _) αψ₂
    (factorizationPullbackIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αψ₂) (fun M => ?_)
  simp [factorizationPullbackIso, ← Functor.map_comp_assoc]

omit [HasWeakSheafify Z.J AddCommGrpCat.{wZ}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{wZ}] in
/-- `Stacks.SheafOfModules.pullbackUnitIsoTransport_square` at
`Stacks.SheafOfModules.factorizationTransportIso`, with the comparison of the factorizations
replaced by a natural transformation `θ` it is equal to. -/
theorem pullbackUnitIsoTransport_square_factorizationTransportIso_of_hom_eq
    (θ : Lψ₁ ⋙ Lφ₁ ⟶ Lψ₂ ⋙ Lφ₂)
    (hθ : (factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂).hom = θ) :
    Lφ₁.map (pullbackUnitIsoTransport ψ₁ αψ₁).hom ≫ (pullbackUnitIsoTransport φ₁ αφ₁).hom =
      θ.app (_root_.SheafOfModules.unit (Tensor.ringSheaf Z.O)) ≫
        Lφ₂.map (pullbackUnitIsoTransport ψ₂ αψ₂).hom ≫
          (pullbackUnitIsoTransport φ₂ αφ₂).hom := by
  subst hθ
  refine pullbackUnitIsoTransport_square φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂
    (factorizationTransportIso φ₁ ψ₁ φ₂ ψ₂ χ τ₁ hτ₁ τ₂ hτ₂ αφ₁ αψ₁ αφ₂ αψ₂) (fun M => ?_)
  simp [factorizationTransportIso, factorizationPullbackIso, ← Functor.map_comp_assoc]

end Square

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **Stacks 03LU is compatible with the square of `a` between étale and Zariski sites**, with
the comparison of the two factorizations written as
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`
(`AlgebraicGeometry.SmallEtale.factorizationTransportIso_zariskiSquare`): the unit companion of
`AlgebraicGeometry.SmallEtale.zariskiSquare_pullbackTensorIsoTransport`. -/
theorem zariskiSquare_pullbackUnitIsoTransport :
    type_of%
      (Stacks.SheafOfModules.pullbackUnitIsoTransport_square_factorizationTransportIso_of_hom_eq
      (toZariskiRingedToposModulesHom B X.obj X.property)
      (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
      (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
      (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
      (fSharpSetComp_zariskiSquareDirectImageIso B a)
      (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
      (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property)
      (associatedModuleBaseChangeIso B a).hom
      (congrArg Iso.hom (factorizationTransportIso_zariskiSquare B a))) :=
  Stacks.SheafOfModules.pullbackUnitIsoTransport_square_factorizationTransportIso_of_hom_eq
    (toZariskiRingedToposModulesHom B X.obj X.property)
    (schemeHom B a).zariskiRingedToposModulesHom (baseChangeRingedToposModulesHom B a)
    (toZariskiRingedToposModulesHom B Y.obj Y.property) (zariskiSquareHom B a) (Iso.refl _)
    (fSharpSetComp_zariskiSquareHom B a) (zariskiSquareDirectImageIso B a)
    (fSharpSetComp_zariskiSquareDirectImageIso B a)
    (pullbackModulesToZariskiIso B X.obj X.property) (schemeHom B a).zariskiPullbackModulesIso
    (pullbackModulesBaseChangeIso B a) (pullbackModulesToZariskiIso B Y.obj Y.property)
    (associatedModuleBaseChangeIso B a).hom
    (congrArg Iso.hom (factorizationTransportIso_zariskiSquare B a))

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **Stacks 03LU round the square of `g`**, with the comparison of the two factorizations
written as the inverse mate of `AlgebraicGeometry.Space.representedModulePullbackIso`: the unit
companion of `AlgebraicGeometry.Space.representedSquare_pullbackTensorIsoTransport_mateEquiv`. -/
theorem representedSquare_pullbackUnitIsoTransport_mateEquiv :
    type_of%
      (Stacks.SheafOfModules.pullbackUnitIsoTransport_square_factorizationPullbackIso_of_hom_eq
      (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)
      (representedReindexPullbackIso B S hS T')
      (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
      (representedReindexPullbackIso B S hS T)
      ((mateEquiv (representedReindexEquivalence B S hS T).toAdjunction
          (representedReindexEquivalence B S hS T').toAdjunction).symm
        (representedSiteModulePullbackIso B S hS g hg).inv)
      (representedSquareModulePullbackIso_hom_eq B S hS g hg)) :=
  Stacks.SheafOfModules.pullbackUnitIsoTransport_square_factorizationPullbackIso_of_hom_eq
      (representedReindexHom B S hS T') (representedSchemeBaseChangeHom B S hS g)
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS g))
      (representedReindexHom B S hS T) (representedSquareHom B S hS g) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS g)
      (representedSquareDirectImageIso B S hS g hg)
      (fSharpSetComp_representedSquareDirectImageIso B S hS g hg)
      (representedReindexPullbackIso B S hS T')
      (SmallEtale.pullbackModulesBaseChangeIso (associatedBigEtaleSite B) g.left)
      (representedReindexPullbackIso B S hS T)
      ((mateEquiv (representedReindexEquivalence B S hS T).toAdjunction
          (representedReindexEquivalence B S hS T').toAdjunction).symm
        (representedSiteModulePullbackIso B S hS g hg).inv)
      (representedSquareModulePullbackIso_hom_eq B S hS g hg)

end AlgebraicGeometry.Space

end
