module

public import StacksFrontier.Deformation.ToposThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction
public import StacksFrontier.Deformation.ToposThickening.TrivialExtensionClass

/-!
# The boundary of an extension class over a complex of thickenings of a ringed topos

Let `(Sh(C), O)` be a ringed topos and let

```
  (Sh(D₁), O'₁) ⟶ (Sh(D₂), O'₂) ⟶ (Sh(D₃), O'₃)
```

be a complex of first order thickenings of it, presented on one site: three first order
thickenings `O'₁`, `O'₂`, `O'₃` of `O` on the site of `Y` and two maps `O'₃ ⟶ O'₂ ⟶ O'₁` of
thickened structure sheaves over `O`, with the induced maps `I₃ ⟶ I₂ ⟶ I₁` of defining ideals
composing to zero. Fix an `O`-module `F`, pairs `(Kₖ, cₖ)` with `cₖ : Iₖ ⊗_O F ⟶ Kₖ`, and a
short exact sequence `0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` of `O`-modules compatible with the `cₖ` through the
two squares of the remark. Given an extension `F'₂` over `O'₂` as in Stacks 08MB with
`c_{F'₂} = c₂`, Stacks 08MJ produces an extension `F'₁` over `O'₁` with `c_{F'₁} = c₁`, and
Stacks 08MI turns `F'₁` into a class `ξ_{F'₁} ∈ Ext¹_O(F, K₁)` using a trivialization of `O'₁`.

The claim of the remark is that the boundary map

```
  ∂ : Ext¹_O(F, K₁) ⟶ Ext²_O(F, K₃)
```

of the short exact sequence `0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` carries `ξ_{F'₁}` to the obstruction class
`o(F, K₃, c₃)` of Stacks 08MF. It is stated here with the trivialization `π` of `O'₁` arbitrary,
and with comparison data at the third thickening — an extension `E₃` of `F` over `O'₃` with a
presentation (`Deformation.ToposThickening.MonoActionPresentation`), a map `w : Q₃ ⟶ K₂` and a
map `χ` into the restriction of `F'₁` — as hypotheses.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickeningComplex`: a sequence of two morphisms of
  first order thickenings of a ringed topos, presented on one site.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.whole`: the composite
  `O'₃ ⟶ O'₁`, read as a morphism of first order thickenings of the base.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.IsComplex`: the condition that the
  two induced maps of defining ideals compose to zero, the complex condition of Stacks 08ML read
  in the one-site presentation.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex.whole_idealMap`: the induced map of
  defining ideals of the composite morphism is the composite of the two induced maps.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.isComplex_iff_whole_idealMap_eq_zero`:
  the complex condition says exactly that the composite morphism induces zero on defining ideals.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.boundary_underlyingExtensionClass`:
  the boundary map `∂` carries `ξ_{F'₁}` to the obstruction class `o(F, K₃, c₃)`.

## References

* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- A complex of first order thickenings of a ringed topos, presented on one site: a morphism
`O'₂ ⟶ O'₁` of first order thickenings of `O` together with a third first order thickening
`O'₃` of `O` and a map `O'₃ ⟶ O'₂` over `O`.

The complex condition itself is
`Deformation.ToposThickening.FirstOrderThickeningComplex.IsComplex`; a sequence of thickenings
without it is the situation of the first sentence of Stacks 08ML. -/
structure FirstOrderThickeningComplex (i : RingedToposHom X Y) where
  /-- The morphism `O'₂ ⟶ O'₁` of first order thickenings of `O`. -/
  lower : MorphismOfFirstOrderThickenings i
  /-- The structure sheaf `O'₃` of the third thickening. -/
  O₃ : Sheaf Y.J CommRingCat.{w'}
  /-- The structure map `O'₃ ⟶ O` of the third thickening. -/
  fSharp₃ : O₃ ⟶ baseRing i
  /-- The morphism `O'₃ ⟶ O'₂` of thickened structure sheaves. -/
  h₃₂ : O₃ ⟶ lower.O₂
  /-- The morphism `O'₃ ⟶ O'₂` lies over the base ringed topos. -/
  comm₃ : h₃₂ ≫ lower.fSharp₂ = fSharp₃
  /-- The third thickening is first order. -/
  third : FirstOrderThickening (reshapeHom i O₃ fSharp₃)

namespace FirstOrderThickeningComplex

variable {i : RingedToposHom X Y} (S : FirstOrderThickeningComplex i)

/-- The first thickening `O'₁` of the complex. -/
noncomputable abbrev first : FirstOrderThickening i := S.lower.first

/-- The second thickening `O'₂` of the complex. -/
noncomputable abbrev second : FirstOrderThickening (reshapeHom i S.lower.O₂ S.lower.fSharp₂) :=
  S.lower.second

/-- The third thickening of the complex, as a thickening of the base presented on the site of
`Y`. -/
abbrev thirdHom : RingedToposHom X (reshape Y S.O₃) := reshapeHom i S.O₃ S.fSharp₃

/-- The morphism `O'₃ ⟶ O'₂` of the complex, read as a morphism of first order thickenings of
the base. -/
def upper : MorphismOfFirstOrderThickenings (reshapeHom i S.lower.O₂ S.lower.fSharp₂) where
  first := S.lower.second
  O₂ := S.O₃
  fSharp₂ := S.fSharp₃
  hSharp := S.h₃₂
  comm := S.comm₃
  second := S.third

/-- The composite `O'₃ ⟶ O'₁` of the two morphisms of the complex, read as a morphism of first
order thickenings of the base. -/
def whole : MorphismOfFirstOrderThickenings i where
  first := S.lower.first
  O₂ := S.O₃
  fSharp₂ := S.fSharp₃
  hSharp := S.h₃₂ ≫ S.lower.hSharp
  comm := by rw [Category.assoc, S.lower.comm, S.comm₃]
  second := S.third

/-- The induced map `I₂ ⟶ I₁` of defining ideals of the complex. -/
noncomputable def idealMap₂₁ : S.lower.second.I ⟶ S.lower.first.I := S.lower.idealMap

/-- The induced map `I₃ ⟶ I₂` of defining ideals of the complex. -/
noncomputable def idealMap₃₂ : S.third.I ⟶ S.lower.second.I := S.upper.idealMap

/-- The induced map of defining ideals of the composite morphism `O'₃ ⟶ O'₁` is the composite
`I₃ ⟶ I₂ ⟶ I₁` of the two induced maps. -/
lemma whole_idealMap : S.whole.idealMap = S.idealMap₃₂ ≫ S.idealMap₂₁ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  refine S.lower.inclOne_injective U ?_
  calc S.whole.inclOne U (S.whole.idealMap.val.app U b)
      = S.whole.ringMapH.hom.app U (S.whole.inclTwo U b) := S.whole.inclOne_idealMap U b
    _ = S.lower.ringMapH.hom.app U (S.upper.ringMapH.hom.app U (S.upper.inclTwo U b)) := by
        show ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map
          (S.h₃₂ ≫ S.lower.hSharp)).hom.app U (S.upper.inclTwo U b) = _
        rw [CategoryTheory.Functor.map_comp]
        rfl
    _ = S.lower.ringMapH.hom.app U (S.upper.inclOne U (S.upper.idealMap.val.app U b)) :=
        congrArg (fun z : (Stacks.SheafOfModules.Tensor.ringSheaf S.lower.O₂).obj.obj U =>
          S.lower.ringMapH.hom.app U z) (S.upper.inclOne_idealMap U b).symm
    _ = S.lower.inclOne U (S.lower.idealMap.val.app U (S.upper.idealMap.val.app U b)) :=
        (S.lower.inclOne_idealMap U (S.upper.idealMap.val.app U b)).symm

/-- A sequence of two morphisms of first order thickenings of a ringed topos, presented on one
site, is a *complex* when the two induced maps of defining ideals compose to zero, so that
`I₃ ⟶ I₂ ⟶ I₁` is a complex of `O`-modules. -/
def IsComplex : Prop := S.idealMap₃₂ ≫ S.idealMap₂₁ = 0

/-- A sequence of two morphisms of first order thickenings is a complex exactly when the
composite morphism `O'₃ ⟶ O'₁` induces the zero map on defining ideals. -/
lemma isComplex_iff_whole_idealMap_eq_zero : S.IsComplex ↔ S.whole.idealMap = 0 := by
  rw [S.whole_idealMap]
  exact Iff.rfl

section Boundary

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf S.O₃))]

omit [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- Let `(Sh(C), O)` be a ringed topos, `F` an `O`-module, and let `O'₃ ⟶ O'₂ ⟶ O'₁` be a
complex of first order thickenings of `(Sh(C), O)` presented on one site, with `π` a
trivialization of `O'₁`. Let `(Kₖ, cₖ)` be pairs with `cₖ : Iₖ ⊗_O F ⟶ Kₖ` and let
`0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` be a short exact sequence of `O`-modules making the two squares `_hc₂₁`
and `hc₃₂` of the remark commute. Let `F'₂` be an extension as in Stacks 08MB over `O'₂` with
`c_{F'₂} = c₂` and let `F'₁` be the extension over `O'₁` that Stacks 08MJ produces from it.

Then the boundary map `∂ : Ext¹_O(F, K₁) ⟶ Ext²_O(F, K₃)` of `0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` — Yoneda
composition with the class of that sequence — carries the class `ξ_{F'₁}` of Stacks 08MI to the
obstruction class `o(F, K₃, c₃)` of Stacks 08MF, for comparison data `Q₃`, `E₃`, `presentation`,
`w`, `hw` and `χ` at the third thickening. -/
@[stacks 08MM "the claim: the boundary of the extension class is the obstruction class"]
theorem boundary_underlyingExtensionClass (_hS : S.IsComplex) (π : Trivialization i)
    (F K₁ K₂ K₃ : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (c₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
      (baseRing i)).obj S.lower.first.I).obj F ⟶ K₁)
    (c₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
      (baseRing i)).obj S.lower.second.I).obj F ⟶ K₂)
    (c₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
      (baseRing i)).obj S.third.I).obj F ⟶ K₃)
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (_hc₂₁ : c₂ ≫ k₂₁ = ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
      (baseRing i)).map S.idealMap₂₁).app F ≫ c₁)
    (hc₃₂ : c₃ ≫ k₃₂ = ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
      (baseRing i)).map S.idealMap₃₂).app F ≫ c₂)
    (E₂ : Abelian.YonedaExtension ((structureRestrict (reshapeHom i S.lower.O₂
        S.lower.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj K₂) 0)
    (_hE₂ : (extensionActionMap S.lower.second E₂).1 = c₂)
    (E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj K₁) 0)
    (_hE₁ : (extensionActionMap S.lower.first E₁).1 = c₁)
    {Q₃ : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
    {E₃ : Abelian.YonedaExtension ((structureRestrict S.thirdHom).obj F)
      ((structureRestrict S.thirdHom).obj Q₃) 0}
    (presentation : MonoActionPresentation S.third E₃) (w : Q₃ ⟶ K₂)
    (hw : (extensionActionMap S.third E₃).1 ≫ w =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
        (baseRing i)).map S.idealMap₃₂).app F ≫ c₂)
    (χ : E₃.Z.left ⟶
      (structureRestrict S.thirdHom).obj ((splitRestriction i S.lower.first π).obj E₁.Z.left))
    (hχf : E₃.f ≫ χ = (structureRestrict S.thirdHom).map (w ≫ k₂₁) ≫
      (structureRestrict S.thirdHom).map (splitExtension i S.lower.first π F K₁ E₁).f)
    (hχg : χ ≫ (structureRestrict S.thirdHom).map
      (splitExtension i S.lower.first π F K₁ E₁).g = E₃.g) :
    (underlyingExtensionClass i S.lower.first π F K₁ E₁).comp hK.extClass (by decide) =
      existenceObstructionClass S.third F K₃ c₃ := by
  classical
  have hex := restrictScalars_exact
    ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map S.thirdHom.fSharp)
  have hlim : PreservesFiniteLimits (structureRestrict S.thirdHom) := hex.1
  have hcolim : PreservesFiniteColimits (structureRestrict S.thirdHom) := hex.2
  have hff := S.third.restrictScalarsFullyFaithful
  have hfull : (structureRestrict S.thirdHom).Full := hff.full
  have hfaith : (structureRestrict S.thirdHom).Faithful := hff.faithful
  have hzero : (extensionActionMap S.third E₃).1 ≫ (w ≫ k₂₁) = 0 := by
    rw [← Category.assoc, hw, ← hc₃₂, Category.assoc, hk, comp_zero]
  obtain ⟨v, hv⟩ : ∃ v : presentation.C ⟶ K₁, presentation.proj ≫ v = w ≫ k₂₁ :=
    ⟨presentation.shortExact.gIsCokernel.desc (CokernelCofork.ofπ (w ≫ k₂₁) hzero),
      presentation.shortExact.gIsCokernel.fac _ WalkingParallelPair.one⟩
  have hξ : underlyingExtensionClass i S.lower.first π F K₁ E₁ =
      (yonedaExtension_shortExact presentation.descent).extClass.comp
        (Abelian.Ext.mk₀ v) (add_zero 1) := by
    apply (structureRestrict S.thirdHom).extMap_injective_of_fullyFaithful F K₁
    rw [Functor.mapExtAddHom_comp_mk₀,
      mapExtAddHom_descent_extClass (Y := reshape Y S.O₃) (i := S.thirdHom)
        presentation.proj presentation.descent presentation.comparison
        presentation.comparison_left presentation.comparison_right,
      Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Functor.map_comp, hv, Functor.mapExtAddHom_apply]
    have hnat := ShortComplex.ShortExact.extClass_naturality
      (yonedaExtension_shortExact E₃)
      ((splitExtension_shortExact i S.lower.first π F K₁ E₁).map_of_exact
        (structureRestrict S.thirdHom))
      { τ₁ := (structureRestrict S.thirdHom).map (w ≫ k₂₁)
        τ₂ := χ
        τ₃ := 𝟙 _
        comm₁₂ := hχf.symm
        comm₂₃ := hχg.trans (Category.comp_id _).symm }
    exact (Abelian.Ext.mapExactFunctor_extClass (structureRestrict S.thirdHom)
      (splitExtension_shortExact i S.lower.first π F K₁ E₁)).trans
      (hnat.trans (Abelian.Ext.mk₀_id_comp _)).symm
  rw [existenceObstructionClass_eq_obstruction S.third F K₃ c₃ presentation]
  exact Abelian.comp_extClass_naturality hK presentation.shortExact
    { τ₁ := c₃
      τ₂ := w
      τ₃ := v
      comm₁₂ := hc₃₂.trans hw.symm
      comm₂₃ := hv.symm }
    (underlyingExtensionClass i S.lower.first π F K₁ E₁)
    (yonedaExtension_shortExact presentation.descent).extClass hξ

end Boundary

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
