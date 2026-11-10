module

public import StacksFrontier.Deformation.ToposThickening.ExtensionRestriction
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundary

/-!
# The boundary of an extension class over a complex of thickenings, for the data of the remark

This file states the claim of Remark Stacks 08MM for the data the remark itself describes: the
extension `F'₂` over the second thickening and the extension `F'₁` over the first that the
functoriality of Stacks 08MJ produces from it, given as an extension receiving a map from `F'₂`
which is `K₂ ⟶ K₁` on kernel modules and the identity on `F`. The comparison data that
`Deformation.ToposThickening.FirstOrderThickeningComplex.boundary_underlyingExtensionClass`
(`StacksFrontier/Deformation/ToposThickening/ThickeningComplexBoundary.lean`) takes as given is
constructed here from `F'₂`.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.boundary_underlyingExtensionClass_of_pushout`: **Stacks 08MM**, for the data of the remark.
* `Deformation.ToposThickening.extensionActionMap_comp_of_hom`: a map of extensions over `F`
  inducing `k` on kernel modules intertwines the two action maps.
* `Deformation.ToposThickening.exists_extension_hom_pair_of_extensions`: two extensions of the
  same module have a common refinement with kernel module the biproduct.

## Implementation notes

Three steps produce the comparison data.

* `E'₃` of the source proof is `F'₂` read over `O'₃` through `O'₃ ⟶ O'₂`, whose action map is
  `((I₃ ⟶ I₂) ⊗ F) ≫ c₂` by
  `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.restrictedExtension_actionMap`,
  hence `c₃ ≫ (K₃ ⟶ K₂)` by the second compatibility square.
* The source enlarges the kernel module into an injective one to make the action map injective.
  Here the enlargement is instead a common refinement with an extension that already has
  injective action map (`exists_extension_hom_pair` against
  `Deformation.ToposThickening.exists_extension_monoActionPresentation`), whose kernel module is
  the biproduct; `w` is the projection onto `K₂`. The obstruction class is computed by any
  presentation (`Deformation.ToposThickening.existenceObstructionClass_eq_obstruction`), so no
  injective module is needed.
* `χ` is the composite `E₃ ⟶ F'₂ ⟶ F'₁`, read over `O'₃`. Its target has to be `F'₁` restricted
  along the trivialization, while the composite restricts it along `O'₃ ⟶ O'₂ ⟶ O'₁`; the two
  agree because `hπ` says that the latter ring map factors as `O'₃ ⟶ O ⟶ O'₁` through the
  trivialization, which is what Stacks 08ML deduces from the complex condition.

The naturality of the action map in a map of extensions and the common refinement of two
extensions are proved in
`StacksFrontier/Deformation/ToposThickening/ModulesOnThickening/FixedAction.lean` only as private
lemmas, which no other module can use; they are proved again here, publicly, as
`Deformation.ToposThickening.extensionActionMap_comp_of_hom` and
`Deformation.ToposThickening.exists_extension_hom_pair_of_extensions`.

## References

* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
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

section Extensions

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  {i : RingedToposHom X Y}

/-- **The action map is natural in a map of extensions.** A map of middle terms over the identity
on the quotient module and a map `k` of kernel modules intertwines the two action maps: the
action of the source extension followed by `k` is the action of the target extension. -/
theorem extensionActionMap_comp_of_hom (hi : FirstOrderThickening i)
    {F K L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F) ((structureRestrict i).obj K) 0)
    (E' : Abelian.YonedaExtension ((structureRestrict i).obj F) ((structureRestrict i).obj L) 0)
    (k : K ⟶ L) (u : E.Z.left ⟶ E'.Z.left)
    (hf : E.f ≫ u = (structureRestrict i).map k ≫ E'.f) (hg : u ≫ E'.g = E.g) :
    (extensionActionMap hi E).1 ≫ k = (extensionActionMap hi E').1 := by
  let D : TwoExtensions i :=
    { thickening := hi, F := F, K := K, G := F, L := L
      firstExtension := E, secondExtension := E'
      quotientMap := 𝟙 F, kernelMap := k }
  have hq : u ≫ E'.g = E.g ≫ (structureRestrict i).map (𝟙 F) := by
    rwa [CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := idealActionMap_naturality D u hf hq
  change (extensionActionMap hi E).1 ≫ k =
    idealTensorHom hi (𝟙 F) ≫ (extensionActionMap hi E').1 at hn
  have hid : idealTensorHom hi (𝟙 F) = 𝟙 _ := by
    let R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)
    have hval : (SheafOfModules.forget R).map (𝟙 F) = 𝟙 F.val :=
      CategoryTheory.Functor.map_id (SheafOfModules.forget R) F
    have h : PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val)
          ((SheafOfModules.forget R).map (𝟙 F)) =
        𝟙 (PresheafOfModulesOfCommRing.Monoidal.tensorObj hi.I.val F.val) := by
      rw [hval]
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro a x
      rfl
    change (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 hi.I.val)
        ((SheafOfModules.forget R).map (𝟙 F))) = 𝟙 _
    rw [h]
    exact CategoryTheory.Functor.map_id _ _
  rwa [hid, Category.id_comp] at hn

variable [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  {F : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- An extension receiving a prescribed class receives a map of extensions: if the class of `E`
pushed forward along `γ` is the class of `E'`, there is a map of middle terms over `F` inducing
`γ` on the kernel modules. -/
private lemma exists_hom_of_extensionClass_comp_eq'
    {Q L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F) ((structureRestrict i).obj Q) 0)
    (E' : Abelian.YonedaExtension ((structureRestrict i).obj F) ((structureRestrict i).obj L) 0)
    (γ : Q ⟶ L)
    (h : (extensionClass F Q E).comp
      (Abelian.Ext.mk₀ ((structureRestrict i).map γ)) (add_zero 1) = extensionClass F L E') :
    ∃ u : E.Z.left ⟶ E'.Z.left,
      E.f ≫ u = (structureRestrict i).map γ ≫ E'.f ∧ u ≫ E'.g = E.g := by
  obtain ⟨E'', u, hu, hg⟩ := Abelian.shortExact_pushout (yonedaExtension_shortExact E)
    ((structureRestrict i).map γ)
  have hcl : extensionClass F L E'' = extensionClass F L E' := by
    refine Eq.trans ?_ h
    have hnat := (yonedaExtension_shortExact E).extClass_naturality
      (yonedaExtension_shortExact E'')
      { τ₁ := (structureRestrict i).map γ
        τ₂ := u, τ₃ := 𝟙 _
        comm₁₂ := hu.symm, comm₂₃ := by simpa using hg }
    simpa only [extensionClass, Abelian.Ext.mk₀_id_comp] using hnat.symm
  obtain ⟨φ, hφ₁, hφ₂⟩ := ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
    (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((structureRestrict i).obj F) ((structureRestrict i).obj L)).2.1 _ _ _ _ _ _ _ _
    (yonedaExtension_shortExact E'') (yonedaExtension_shortExact E')).1 hcl
  refine ⟨u ≫ φ.hom, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ φ.hom) hu).trans
        ((Category.assoc _ _ _).trans (congrArg (fun z => _ ≫ z) hφ₁)))
  · exact (Category.assoc _ _ _).trans ((congrArg (fun z => u ≫ z) hφ₂).trans hg)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- **A common refinement of two extensions of the same module.** Realize the sum of the two
classes pushed into the biproduct of the two kernel modules by an extension; it maps to both
extensions, because each projection of the biproduct kills the other summand. -/
theorem exists_extension_hom_pair_of_extensions
    {Q₁ Q₂ : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
    (E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F) ((structureRestrict i).obj Q₁) 0)
    (E₂ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q₂) 0) :
    ∃ (E₃ : Abelian.YonedaExtension ((structureRestrict i).obj F)
        ((structureRestrict i).obj (Q₁ ⊞ Q₂)) 0)
      (u₁ : E₃.Z.left ⟶ E₁.Z.left) (u₂ : E₃.Z.left ⟶ E₂.Z.left),
      (E₃.f ≫ u₁ = (structureRestrict i).map biprod.fst ≫ E₁.f ∧ u₁ ≫ E₁.g = E₃.g) ∧
        E₃.f ≫ u₂ = (structureRestrict i).map biprod.snd ≫ E₂.f ∧ u₂ ≫ E₂.g = E₃.g := by
  obtain ⟨M, f, g, z, h, hx⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).1
      ((extensionClass F Q₁ E₁).comp
          (Abelian.Ext.mk₀ ((structureRestrict i).map biprod.inl)) (add_zero 1) +
        (extensionClass F Q₂ E₂).comp
          (Abelian.Ext.mk₀ ((structureRestrict i).map biprod.inr)) (add_zero 1))
  let E₃ := Abelian.shortExactYonedaExtension h
  have hE₃ : extensionClass F (Q₁ ⊞ Q₂) E₃ = _ := hx
  refine (fun ⟨u₁, hu₁, hg₁⟩ ⟨u₂, hu₂, hg₂⟩ => ⟨E₃, u₁, u₂, ⟨hu₁, hg₁⟩, hu₂, hg₂⟩)
    (exists_hom_of_extensionClass_comp_eq' E₃ E₁ biprod.fst ?_)
    (exists_hom_of_extensionClass_comp_eq' E₃ E₂ biprod.snd ?_)
  all_goals
    rw [hE₃]
    simp only [Abelian.Ext.add_comp, Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, ← CategoryTheory.Functor.map_comp, biprod.inl_fst,
      biprod.inr_fst, biprod.inl_snd, biprod.inr_snd, CategoryTheory.Functor.map_zero,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, add_zero, zero_add,
      CategoryTheory.Functor.map_id, Abelian.Ext.comp_mk₀_id]

end Extensions

namespace FirstOrderThickeningComplex

variable {i : RingedToposHom X Y} (S : FirstOrderThickeningComplex i)

section Boundary

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf S.O₃))]

omit [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **Stacks Project, Tag 08MM.** The claim of the remark, for the data of the remark. Let
`(Sh(C), O)` be a ringed topos, `F` an `O`-module, and let `O'₃ ⟶ O'₂ ⟶ O'₁` be a complex of
first order thickenings of `(Sh(C), O)` presented on one site. Let `π` be a trivialization of
`O'₁` through which the composite `O'₃ ⟶ O'₁` factors, which is the canonical trivialization a
complex supplies by Stacks 08ML. Let `(Kₖ, cₖ)` be pairs with `cₖ : Iₖ ⊗_O F ⟶ Kₖ` and let
`0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` be a short exact sequence of `O`-modules making the second square
`hc₃₂` of the remark commute. Let `F'₂` be an extension as in Stacks 08MB over `O'₂` with
`c_{F'₂} = c₂`, and let `F'₁` be the extension over `O'₁` that the functoriality of Stacks 08MJ
produces from it: an extension receiving a map `u` from `F'₂` which is `K₂ ⟶ K₁` on kernel
modules and the identity on `F`.

Then the boundary map `∂ : Ext¹_O(F, K₁) ⟶ Ext²_O(F, K₃)` of `0 ⟶ K₃ ⟶ K₂ ⟶ K₁ ⟶ 0` — Yoneda
composition with the class of that sequence — carries the class `ξ_{F'₁}` of Stacks 08MI to the
obstruction class `o(F, K₃, c₃)` of Stacks 08MF.

The comparison data of
`Deformation.ToposThickening.FirstOrderThickeningComplex.boundary_underlyingExtensionClass` is
built here out of `F'₂`; see the module docstring for the three steps. The first square of the
remark and the action map `c₁` of `F'₁` are consequences of the pushout square rather than
hypotheses. -/
theorem boundary_underlyingExtensionClass_of_pushout (hS : S.IsComplex) (π : Trivialization i)
    (hπ : S.upper.ringMapH ≫ S.lower.ringMapH =
      S.whole.ringMap₂ ≫ splittingRingHom i S.lower.first π)
    (F K₁ K₂ K₃ : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (c₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
      S.lower.second.I ⟶ K₂)
    (c₃ : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.third.I ⟶ K₃)
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (hc₃₂ : c₃ ≫ k₃₂ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₃₂ ≫ c₂)
    (E₂ : Abelian.YonedaExtension
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj K₂) 0)
    (hE₂ : (extensionActionMap S.lower.second E₂).1 = c₂)
    (E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj K₁) 0)
    (u : E₂.Z.left ⟶ (S.lower.restrictedExtension E₁).Z.left)
    (hu : E₂.f ≫ u =
      (structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).map k₂₁ ≫
        (S.lower.restrictedExtension E₁).f)
    (hug : u ≫ (S.lower.restrictedExtension E₁).g = E₂.g) :
    (underlyingExtensionClass i S.lower.first π F K₁ E₁).comp hK.extClass (by decide) =
      existenceObstructionClass S.third F K₃ c₃ := by
  classical
  -- `F'₂` read over the third thickening is the source's `E'₃`, with action map `c₃ ≫ k₃₂`
  have hT : (extensionActionMap S.third (S.upper.restrictedExtension E₂)).1 =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₃₂ ≫ c₂ :=
    (S.upper.restrictedExtension_actionMap E₂).trans
      (congrArg (fun z =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₃₂ ≫ z)
        hE₂)
  -- the first square of the remark, for the action map of `F'₁`
  have hc₂₁ : c₂ ≫ k₂₁ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₂₁ ≫
        (extensionActionMap S.lower.first E₁).1 := by
    rw [← hE₂]
    exact (extensionActionMap_comp_of_hom S.lower.second E₂ (S.lower.restrictedExtension E₁) k₂₁
      u hu hug).trans (S.lower.restrictedExtension_actionMap E₁)
  -- a presentation at the third thickening whose extension maps to `F'₂` read there
  obtain ⟨Q, Eb, ⟨P⟩⟩ := exists_extension_monoActionPresentation S.third F
  obtain ⟨E₃, u₁, u₂, ⟨hu₁, hg₁⟩, hu₂, hg₂⟩ :=
    exists_extension_hom_pair_of_extensions Eb (S.upper.restrictedExtension E₂)
  have hd₁ : (extensionActionMap S.third E₃).1 ≫ biprod.fst =
      (extensionActionMap S.third Eb).1 :=
    extensionActionMap_comp_of_hom S.third E₃ Eb biprod.fst u₁ hu₁ hg₁
  have hmono : Mono (extensionActionMap S.third Eb).1 := P.shortExact.mono_f
  obtain ⟨P₃⟩ := exists_monoActionPresentation S.third E₃ (mono_of_mono_fac hd₁)
  have hw : (extensionActionMap S.third E₃).1 ≫ biprod.snd =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₃₂ ≫ c₂ :=
    (extensionActionMap_comp_of_hom S.third E₃ (S.upper.restrictedExtension E₂) biprod.snd u₂
      hu₂ hg₂).trans hT
  -- the comparison `χ` is `E₃ ⟶ F'₂ ⟶ F'₁` read over the third thickening; its target is
  -- `F'₁` restricted along the trivialization, which `hπ` identifies with `F'₁` restricted
  -- along `O'₃ ⟶ O'₂ ⟶ O'₁`
  let ι : (SheafOfModules.restrictScalars S.upper.ringMapH).obj
        ((SheafOfModules.restrictScalars S.lower.ringMapH).obj E₁.Z.left) ≅
      (structureRestrict S.thirdHom).obj
        ((splitRestriction i S.lower.first π).obj E₁.Z.left) :=
    (Stacks.SheafOfModules.restrictScalarsCompIso S.upper.ringMapH S.lower.ringMapH
          (S.whole.ringMap₂ ≫ splittingRingHom i S.lower.first π) hπ.symm E₁.Z.left).symm ≪≫
      Stacks.SheafOfModules.restrictScalarsCompIso S.whole.ringMap₂
        (splittingRingHom i S.lower.first π)
        (S.whole.ringMap₂ ≫ splittingRingHom i S.lower.first π) rfl E₁.Z.left
  let χ : E₃.Z.left ⟶ (structureRestrict S.thirdHom).obj
      ((splitRestriction i S.lower.first π).obj E₁.Z.left) :=
    u₂ ≫ (SheafOfModules.restrictScalars S.upper.ringMapH).map u ≫ ι.hom
  have hχf : E₃.f ≫ χ =
      (structureRestrict S.thirdHom).map (biprod.snd ≫ k₂₁) ≫
        (structureRestrict S.thirdHom).map (splitExtension i S.lower.first π F K₁ E₁).f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext z
    let y : K₂.val.obj U := (biprod.snd : (Q ⊞ K₂) ⟶ K₂).val.app U z
    have h2 : u₂.val.app U (E₃.f.val.app U z) = E₂.f.val.app U y :=
      congrArg (fun m : (structureRestrict S.thirdHom).obj (Q ⊞ K₂) ⟶
        (S.upper.restrictedExtension E₂).Z.left => m.val.app U z) hu₂
    have h1 : u.val.app U (E₂.f.val.app U y) = E₁.f.val.app U (k₂₁.val.app U y) :=
      congrArg (fun m : (structureRestrict
          (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj K₂ ⟶
          (S.lower.restrictedExtension E₁).Z.left =>
        m.val.app U y) hu
    change u.val.app U (u₂.val.app U (E₃.f.val.app U z)) =
      E₁.f.val.app U (k₂₁.val.app U y)
    rwa [h2]
  have hχg : χ ≫ (structureRestrict S.thirdHom).map
      (splitExtension i S.lower.first π F K₁ E₁).g = E₃.g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext z
    have h2 : E₂.g.val.app U (u₂.val.app U z) = E₃.g.val.app U z :=
      congrArg (fun m : E₃.Z.left ⟶ (structureRestrict S.thirdHom).obj F =>
        m.val.app U z) hg₂
    have h1 : E₁.g.val.app U (u.val.app U (u₂.val.app U z)) =
        E₂.g.val.app U (u₂.val.app U z) :=
      congrArg (fun m : E₂.Z.left ⟶ (structureRestrict
          (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj F =>
        m.val.app U (u₂.val.app U z)) hug
    change E₁.g.val.app U (u.val.app U (u₂.val.app U z)) = E₃.g.val.app U z
    rwa [h1]
  exact S.boundary_underlyingExtensionClass hS π F K₁ K₂ K₃
    (extensionActionMap S.lower.first E₁).1 c₂ c₃ k₃₂ k₂₁ hk hK hc₂₁ hc₃₂ E₂ hE₂ E₁ rfl
    P₃ biprod.snd hw χ hχf hχg

end Boundary

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
