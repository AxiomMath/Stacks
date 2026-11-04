module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare

/-!
# Base change of right Kan extensions of sheaves of modules

Let

```
  𝒳' --g'--> 𝒳
  |          |
  f'         f
  v          v
  𝒴' --g---> 𝒴
```

be a square of sites commuting up to a `2`-cell `w : g' ⋙ f ⟶ f' ⋙ g`, carrying sheaves of rings
`O_𝒳, O_𝒴, O_𝒴', O_𝒳'` with `O_𝒳 = f⁻¹ O_𝒴`, `O_𝒴' = g⁻¹ O_𝒴`, `O_𝒳' = f'⁻¹ O_𝒴'` and
`O_𝒳' = g'⁻¹ O_𝒳` on underlying presheaves of rings. Let `f_*` and `f'_*` be direct images of
sheaves of modules whose underlying abelian presheaves are the right Kan extensions along `f.op`
and `f'.op`, and whose module structures are the expected ones on the legs of the limits
computing those Kan extensions: a section `r` over `y` acts on the leg at `(x, y ⟶ f x)` through
its restriction to `x`.

The base change of right Kan extensions along the opposite square,
`CategoryTheory.TwoSquare.ranBaseChange`, then underlies a morphism of sheaves of modules
`g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ`, natural in `ℱ`, as soon as the four ring identifications are
compatible with the `2`-cell on the legs; and it is an isomorphism whenever the base change of
right Kan extensions is, for instance when the square is Guitart exact.

## Main definitions

* `Stacks.SheafOfModules.directImageBaseChange`: the base change transformation
  `g⁻¹ ∘ f_* ⟶ f'_* ∘ (g')⁻¹` of sheaves of modules.

## Main results

* `Stacks.SheafOfModules.ranBaseChange_smul`: the base change of right Kan extensions is linear
  for the module structures read on the legs.
* `Stacks.SheafOfModules.isIso_directImageBaseChange`: the base change transformation is an
  isomorphism when the base change of right Kan extensions is.

## References

* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

section Legs

universe t v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ r

variable {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  {𝒴' : Type v₃} [Category.{w₃} 𝒴'] {𝒳' : Type v₄} [Category.{w₄} 𝒳']
  {f : 𝒳 ⥤ 𝒴} {g : 𝒴' ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒳' ⥤ 𝒳} (w : TwoSquare g' f' f g)
  {RX : 𝒳ᵒᵖ ⥤ RingCat.{r}} {RY : 𝒴ᵒᵖ ⥤ RingCat.{r}} {RY' : 𝒴'ᵒᵖ ⥤ RingCat.{r}}
  {RX' : 𝒳'ᵒᵖ ⥤ RingCat.{r}}
  [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, f.op.HasPointwiseRightKanExtension F]
  [∀ F : 𝒳'ᵒᵖ ⥤ AddCommGrpCat.{t}, f'.op.HasPointwiseRightKanExtension F]
  [∀ F : 𝒳'ᵒᵖ ⥤ AddCommGrpCat.{t}, f'.op.HasRightKanExtension F]
  [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, f.op.HasRightKanExtension F]

omit [∀ (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat), f.op.HasPointwiseRightKanExtension F] in
/-- **Linearity of the base change of right Kan extensions, read on legs.** If the actions of
sections on `N` and `K` are read on the legs of the limits computing the Kan extensions, as in
`legN` and `legK`, and the ring identifications are compatible with the `2`-cell, as in `hsc`,
then the base change of right Kan extensions, conjugated by `βN` and `βK`, commutes with the
action of `r`. -/
theorem ranBaseChange_smul (hf : RX = f.op ⋙ RY) (hg : RY' = g.op ⋙ RY)
    (hf' : RX' = f'.op ⋙ RY') (hg' : RX' = g'.op ⋙ RX)
    (M : PresheafOfModules.{t} RX) (N : PresheafOfModules.{t} RY)
    (K : PresheafOfModules.{t} RY')
    (βN : N.presheaf ≅ f.op.ran.obj M.presheaf)
    (βK : K.presheaf ≅ f'.op.ran.obj (g'.op ⋙ M.presheaf))
    (legN : ∀ (y : 𝒴ᵒᵖ) (j : StructuredArrow y f.op) (r : RY.obj y) (s : N.obj y),
      Stacks.SheafOfModules.ranπ f.op M.presheaf y j (βN.hom.app y (r • s)) =
        (eqToHom hf.symm).app j.right (RY.map j.hom r) •
          (Stacks.SheafOfModules.ranπ f.op M.presheaf y j (βN.hom.app y s) : M.obj j.right))
    (legK : ∀ (y : 𝒴'ᵒᵖ) (j : StructuredArrow y f'.op) (r : RY'.obj y) (s : K.obj y),
      Stacks.SheafOfModules.ranπ f'.op (g'.op ⋙ M.presheaf) y j (βK.hom.app y (r • s)) =
        (show RX.obj (g'.op.obj j.right) from
            (eqToHom hg').app j.right ((eqToHom hf'.symm).app j.right (RY'.map j.hom r))) •
          (show M.obj (g'.op.obj j.right) from
            Stacks.SheafOfModules.ranπ f'.op (g'.op ⋙ M.presheaf) y j (βK.hom.app y s)))
    (hsc : ∀ (y : 𝒴'ᵒᵖ) (j : StructuredArrow y f'.op) (r : RY'.obj y),
      (eqToHom hf.symm).app (g'.op.obj j.right)
          (RY.map (g.op.map j.hom ≫ w.op.natTrans.app j.right) ((eqToHom hg).app y r)) =
        (eqToHom hg').app j.right ((eqToHom hf'.symm).app j.right (RY'.map j.hom r)))
    (y : 𝒴'ᵒᵖ) (r : RY'.obj y) (s : N.obj (g.op.obj y)) :
    βK.inv.app y ((w.op.ranBaseChange.app M.presheaf).app y
        (βN.hom.app (g.op.obj y) ((eqToHom hg).app y r • s))) =
      r • (βK.inv.app y ((w.op.ranBaseChange.app M.presheaf).app y
        (βN.hom.app (g.op.obj y) s)) : K.obj y) := by
  have inj : Function.Injective (βK.hom.app y) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hi : ∀ z, βK.hom.app y (βK.inv.app y z) = z := fun z ↦ by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
      CategoryTheory.id_apply]
  have hb : ∀ (z : (f.op.ran.obj M.presheaf).obj (g.op.obj y)) (j : StructuredArrow y f'.op),
      Stacks.SheafOfModules.ranπ f'.op (g'.op ⋙ M.presheaf) y j
        ((w.op.ranBaseChange.app M.presheaf).app y z) =
      Stacks.SheafOfModules.ranπ f.op M.presheaf (g.op.obj y)
        (StructuredArrow.mk (g.op.map j.hom ≫ w.op.natTrans.app j.right)) z := fun z j ↦ by
    rw [← ConcreteCategory.comp_apply, Stacks.SheafOfModules.ranBaseChange_π]
  apply inj
  rw [hi]
  refine Concrete.isLimit_ext _ (Stacks.SheafOfModules.ranIsLimit f'.op _ y) _ _ fun j ↦ ?_
  change Stacks.SheafOfModules.ranπ f'.op (g'.op ⋙ M.presheaf) y j _ =
    Stacks.SheafOfModules.ranπ f'.op (g'.op ⋙ M.presheaf) y j _
  refine (hb _ j).trans ((legN _ _ _ _).trans (Eq.trans ?_ (legK y j r _).symm))
  rw [hi, hb]
  exact congrArg (· • _) (hsc y j r)

end Legs

section DirectImage

universe t v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ r

variable {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  {𝒴' : Type v₃} [Category.{w₃} 𝒴'] {𝒳' : Type v₄} [Category.{w₄} 𝒳']
  {f : 𝒳 ⥤ 𝒴} {g : 𝒴' ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒳' ⥤ 𝒳} (w : TwoSquare g' f' f g)
  {JX : GrothendieckTopology 𝒳} {JY : GrothendieckTopology 𝒴} {JY' : GrothendieckTopology 𝒴'}
  {JX' : GrothendieckTopology 𝒳'} [g.IsContinuous JY' JY] [g'.IsContinuous JX' JX]
  {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}} {OY' : Sheaf JY' RingCat.{r}}
  {OX' : Sheaf JX' RingCat.{r}}
  [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, f.op.HasPointwiseRightKanExtension F]
  [∀ F : 𝒳'ᵒᵖ ⥤ AddCommGrpCat.{t}, f'.op.HasPointwiseRightKanExtension F]
  [∀ F : 𝒳'ᵒᵖ ⥤ AddCommGrpCat.{t}, f'.op.HasRightKanExtension F]
  [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{t}, f.op.HasRightKanExtension F]
  (hf : OX.obj = f.op ⋙ OY.obj) (hg : OY'.obj = g.op ⋙ OY.obj)
  (hf' : OX'.obj = f'.op ⋙ OY'.obj) (hg' : OX'.obj = g'.op ⋙ OX.obj)
  (P : SheafOfModules.{t} OX ⥤ SheafOfModules.{t} OY)
  (P' : SheafOfModules.{t} OX' ⥤ SheafOfModules.{t} OY')
  (βP : P ⋙ SheafOfModules.forget OY ⋙ PresheafOfModules.toPresheaf OY.obj ≅
    (SheafOfModules.forget OX ⋙ PresheafOfModules.toPresheaf OX.obj) ⋙ f.op.ran)
  (βP' : P' ⋙ SheafOfModules.forget OY' ⋙ PresheafOfModules.toPresheaf OY'.obj ≅
    (SheafOfModules.forget OX' ⋙ PresheafOfModules.toPresheaf OX'.obj) ⋙ f'.op.ran)

/-- The presheaf-level base change transformation `g⁻¹ ∘ f_* ⟶ f'_* ∘ (g')⁻¹` for direct images
of sheaves of modules computed by right Kan extensions. -/
noncomputable def directImageBaseChangeToPresheaf :
    (P ⋙ SheafOfModules.pushforward.{t} (F := g) (K := JY) ⟨eqToHom hg⟩) ⋙
        SheafOfModules.forget OY' ⋙ PresheafOfModules.toPresheaf OY'.obj ⟶
      (SheafOfModules.pushforward.{t} (F := g') (K := JX) ⟨eqToHom hg'⟩ ⋙ P') ⋙
        SheafOfModules.forget OY' ⋙ PresheafOfModules.toPresheaf OY'.obj :=
  Functor.whiskerRight βP.hom ((Functor.whiskeringLeft _ _ _).obj g.op) ≫
    Functor.whiskerLeft (SheafOfModules.forget OX ⋙ PresheafOfModules.toPresheaf OX.obj)
      w.op.ranBaseChange ≫
    Functor.whiskerLeft (SheafOfModules.pushforward.{t} (F := g') (K := JX) ⟨eqToHom hg'⟩) βP'.inv

variable
  (legP : ∀ (M : SheafOfModules.{t} OX) (y : 𝒴ᵒᵖ) (j : StructuredArrow y f.op) (r : OY.obj.obj y)
      (s : (P.obj M).val.obj y),
    Stacks.SheafOfModules.ranπ f.op M.val.presheaf y j ((βP.hom.app M).app y (r • s)) =
      (eqToHom hf.symm).app j.right (OY.obj.map j.hom r) •
        (show M.val.obj j.right from
          Stacks.SheafOfModules.ranπ f.op M.val.presheaf y j ((βP.hom.app M).app y s)))
  (legP' : ∀ (M : SheafOfModules.{t} OX') (y : 𝒴'ᵒᵖ) (j : StructuredArrow y f'.op)
      (r : OY'.obj.obj y) (s : (P'.obj M).val.obj y),
    Stacks.SheafOfModules.ranπ f'.op M.val.presheaf y j ((βP'.hom.app M).app y (r • s)) =
      (eqToHom hf'.symm).app j.right (OY'.obj.map j.hom r) •
        (show M.val.obj j.right from
          Stacks.SheafOfModules.ranπ f'.op M.val.presheaf y j ((βP'.hom.app M).app y s)))
  (hsc : ∀ (y : 𝒴'ᵒᵖ) (j : StructuredArrow y f'.op) (r : OY'.obj.obj y),
    (eqToHom hf.symm).app (g'.op.obj j.right)
        (OY.obj.map (g.op.map j.hom ≫ w.op.natTrans.app j.right) ((eqToHom hg).app y r)) =
      (eqToHom hg').app j.right ((eqToHom hf'.symm).app j.right (OY'.obj.map j.hom r)))

/-- The base change morphism `g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ` of sheaves of modules, for direct images
computed by right Kan extensions with the expected module structure on the legs. -/
noncomputable def directImageBaseChangeApp (M : SheafOfModules.{t} OX) :
    (P ⋙ SheafOfModules.pushforward.{t} (F := g) (K := JY) ⟨eqToHom hg⟩).obj M ⟶
      (SheafOfModules.pushforward.{t} (F := g') (K := JX) ⟨eqToHom hg'⟩ ⋙ P').obj M :=
  ⟨PresheafOfModules.homMk
    ((directImageBaseChangeToPresheaf w hg hg' P P' βP βP').app M)
    (fun y r s ↦ ranBaseChange_smul w hf hg hf' hg' M.val (P.obj M).val
      (P'.obj ((SheafOfModules.pushforward.{t} (F := g') (K := JX) ⟨eqToHom hg'⟩).obj M)).val
      (βP.app M) (βP'.app _) (legP M) (legP' _) hsc y r s)⟩

omit [∀ (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat), f.op.HasPointwiseRightKanExtension F] in
/-- On underlying abelian presheaves, the base change morphism is the base change of right Kan
extensions, conjugated by the identifications of the two direct images with Kan extensions. -/
theorem directImageBaseChangeApp_toPresheaf (M : SheafOfModules.{t} OX) :
    (SheafOfModules.forget OY' ⋙ PresheafOfModules.toPresheaf OY'.obj).map
        (directImageBaseChangeApp w hf hg hf' hg' P P' βP βP' legP legP' hsc M) =
      (directImageBaseChangeToPresheaf w hg hg' P P' βP βP').app M := rfl

/-- The base change transformation `g⁻¹ ∘ f_* ⟶ f'_* ∘ (g')⁻¹` of sheaves of modules. -/
noncomputable def directImageBaseChange :
    P ⋙ SheafOfModules.pushforward.{t} (F := g) (K := JY) ⟨eqToHom hg⟩ ⟶
      SheafOfModules.pushforward.{t} (F := g') (K := JX) ⟨eqToHom hg'⟩ ⋙ P' where
  app := directImageBaseChangeApp w hf hg hf' hg' P P' βP βP' legP legP' hsc
  naturality {M M'} u := by
    apply (SheafOfModules.forget OY' ⋙ PresheafOfModules.toPresheaf OY'.obj).map_injective
    rw [Functor.map_comp, Functor.map_comp, directImageBaseChangeApp_toPresheaf,
      directImageBaseChangeApp_toPresheaf]
    exact (directImageBaseChangeToPresheaf w hg hg' P P' βP βP').naturality u

omit [∀ (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat), f.op.HasPointwiseRightKanExtension F] in
/-- The base change transformation is invertible when the base change of right Kan extensions
along the opposite square is. -/
theorem isIso_directImageBaseChange [IsIso (w.op.ranBaseChange (D := AddCommGrpCat.{t}))] :
    IsIso (directImageBaseChange w hf hg hf' hg' P P' βP βP' legP legP' hsc) := by
  have hφ : IsIso (directImageBaseChangeToPresheaf w hg hg' P P' βP βP') :=
    (Functor.isoWhiskerRight βP ((Functor.whiskeringLeft _ _ _).obj g.op) ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.forget OX ⋙ PresheafOfModules.toPresheaf OX.obj)
        (asIso (w.op.ranBaseChange (D := AddCommGrpCat.{t}))) ≪≫
      Functor.isoWhiskerLeft
        (SheafOfModules.pushforward.{t} (F := g') (K := JX) ⟨eqToHom hg'⟩) βP'.symm).isIso_hom
  have : ∀ M, IsIso ((SheafOfModules.forget OY' ⋙ PresheafOfModules.toPresheaf OY'.obj).map
      ((directImageBaseChange w hf hg hf' hg' P P' βP βP' legP legP' hsc).app M)) := fun M ↦
    inferInstanceAs (IsIso ((directImageBaseChangeToPresheaf w hg hg' P P' βP βP').app M))
  have : ∀ M, IsIso ((directImageBaseChange w hf hg hf' hg' P P' βP βP' legP legP' hsc).app M) :=
    fun M ↦ by
      have h := this M
      simp only [Functor.comp_map] at h
      have := isIso_of_reflects_iso
        ((SheafOfModules.forget OY').map
          ((directImageBaseChange w hf hg hf' hg' P P' βP βP' legP legP' hsc).app M))
        (PresheafOfModules.toPresheaf OY'.obj)
      exact isIso_of_reflects_iso _ (SheafOfModules.forget OY')
  exact NatIso.isIso_of_isIso_app _

end DirectImage

end Stacks.SheafOfModules

end
