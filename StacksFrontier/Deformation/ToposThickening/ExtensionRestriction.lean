module

public import StacksFrontier.Deformation.ToposThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ActionMapUnique
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction
public import StacksFrontier.Deformation.ToposThickening.TrivializedThickeningComparison

/-!
# Reading an extension back along a morphism of first order thickenings

Let `(Sh(C), O)` be a ringed topos with two first order thickenings `O'₁` and `O'₂` presented on
one site and a morphism `h^♯ : O'₂ ⟶ O'₁` of thickenings over it, as in
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings`, and let `I₂ ⟶ I₁` be the induced
map of defining ideals. An extension

```
  0 ⟶ K ⟶ F' ⟶ F ⟶ 0
```

of `O'₁`-modules as in Stacks 08MB may be read as a sequence of `O'₂`-modules along `h^♯`; it is
again an extension as in Stacks 08MB, and this file computes its canonical action map: it is the
action map of `F'` precomposed with `(I₂ ⟶ I₁) ⊗ F`.

This is the step `Set E'₃ = E'₂ but viewed as an `O'₃`-module via `O'₃ ⟶ O'₂`. Then
`c_{E'₃} = j ∘ c₃`' of the proof of **Stacks 08MM**, where the conclusion `c_{E'₃} = j ∘ c₃`
comes out of the identity proved here together with the compatibility square relating `c₃` and
`c₂`.

## Main definitions

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.restrictHIso`: an `O`-module read
  along the structure map of the first thickening and then along `h^♯` is that module read along
  the structure map of the second thickening — the commuting square of the morphism of
  thickenings, read on modules.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.restrictedExtension`: the
  extension over the first thickening, read over the second.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.restrictedExtension_actionMap`:
  the canonical action map of the restricted extension is
  `((I₂ ⟶ I₁) ⊗ F) ≫ c_{F'}`.

## Implementation notes

Restriction of scalars along a composite of maps of sheaves of rings is not the composite of the
two restrictions on the nose, so the outer terms of the restricted sequence are reindexed by
`restrictHIso`, which is `Stacks.SheafOfModules.restrictScalarsCompIso`
(`StacksFrontier/Deformation/ToposThickening/TrivializedThickeningComparison.lean`); the composite
`h^♯ ≫ (O'₁ ⟶ O)` is the structure map `O'₂ ⟶ O` only through the commuting square
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.comm` of the morphism of
thickenings, so the reindexing cannot be avoided. Like
`Deformation.ToposThickening.splitRestrictionRestrictScalarsIso` it is the identity map on every
section, so it involves no choice.

The action map is identified through
`Deformation.ToposThickening.extensionActionMap_unique`: the characterizing local formula for
the restricted extension at a section `b` of `I₂` is the formula for `F'` at the section of `I₁`
cut out by `b`, because multiplication by `b` on a module restricted along `h^♯` is
multiplication by `h^♯(b)`, and
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.inclOne_idealMap` says that
`h^♯(b)` is the image of `b` under the induced map of defining ideals.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

namespace MorphismOfFirstOrderThickenings

variable {i : RingedToposHom X Y} (D : MorphismOfFirstOrderThickenings i)
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-- An `O`-module read along the structure map of the first thickening and then along `h^♯` is
that module read along the structure map of the second thickening: the two composites of ring
maps agree by the commuting square of the morphism of thickenings. -/
noncomputable def restrictHIso
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))) :
    (SheafOfModules.restrictScalars D.ringMapH).obj ((structureRestrict i).obj M) ≅
      (structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).obj M :=
  (Stacks.SheafOfModules.restrictScalarsCompIso D.ringMapH (structureRingMap i) D.ringMap₂
    D.ringMapH_comp_structureRingMap.symm M).symm

variable {F K : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))}
  (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
    ((structureRestrict i).obj K) 0)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- The two maps of the extension, restricted along `h^♯` and composed with the identifications
of the outer terms, compose to zero. -/
theorem restrictedShortComplex_zero :
    ((D.restrictHIso K).inv ≫ (SheafOfModules.restrictScalars D.ringMapH).map E.f) ≫
      ((SheafOfModules.restrictScalars D.ringMapH).map E.g ≫ (D.restrictHIso F).hom) = 0 := by
  rw [Category.assoc, ← Category.assoc ((SheafOfModules.restrictScalars D.ringMapH).map E.f),
    ← Functor.map_comp, yonedaExtension_comp_zero E, Functor.map_zero, zero_comp, comp_zero]

/-- An extension `0 ⟶ K ⟶ F' ⟶ F ⟶ 0` of `O'₁`-modules as in Stacks 08MB, read along `h^♯` as
an extension of `O'₂`-modules. -/
noncomputable def restrictedExtension :
    Abelian.YonedaExtension
      ((structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i D.O₂ D.fSharp₂)).obj K) 0 :=
  letI hex := restrictScalars_exact D.ringMapH
  letI : PreservesFiniteLimits (SheafOfModules.restrictScalars D.ringMapH) := hex.1
  letI : PreservesFiniteColimits (SheafOfModules.restrictScalars D.ringMapH) := hex.2
  letI hSE : (ShortComplex.mk _ _ (D.restrictedShortComplex_zero E)).ShortExact := by
    refine ShortComplex.shortExact_of_iso ?_
      ((yonedaExtension_shortExact E).map_of_exact
        (SheafOfModules.restrictScalars D.ringMapH))
    refine ShortComplex.isoMk (D.restrictHIso K) (Iso.refl _) (D.restrictHIso F) ?_ ?_
    · exact (Iso.hom_inv_id_assoc (D.restrictHIso K)
        ((SheafOfModules.restrictScalars D.ringMapH).map E.f)).trans (Category.comp_id _).symm
    · exact Category.id_comp _
  { Z := ComposableArrows.mk₀ ((SheafOfModules.restrictScalars D.ringMapH).obj E.Z.left)
    f := (D.restrictHIso K).inv ≫ (SheafOfModules.restrictScalars D.ringMapH).map E.f
    g := (SheafOfModules.restrictScalars D.ringMapH).map E.g ≫ (D.restrictHIso F).hom
    mono_f := hSE.mono_f
    exact := ComposableArrows.exact₁ _
    exact_g := hSE.exact.exact_toComposableArrows
    epi_g := hSE.epi_g }

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- The first morphism of the restricted extension: the restriction of `E.f`, precomposed with
the identification of the restricted kernel. -/
@[simp]
theorem restrictedExtension_f : (D.restrictedExtension E).f =
    (D.restrictHIso K).inv ≫ (SheafOfModules.restrictScalars D.ringMapH).map E.f := rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- The second morphism of the restricted extension: the restriction of `E.g`, followed by the
identification of the restricted quotient. -/
@[simp]
theorem restrictedExtension_g : (D.restrictedExtension E).g =
    (SheafOfModules.restrictScalars D.ringMapH).map E.g ≫ (D.restrictHIso F).hom := rfl

/-- **The action map of an extension read back along a morphism of first order thickenings.**
An extension of `F` by `K` over the first thickening, read over the second thickening along
`h^♯`, has canonical action map `((I₂ ⟶ I₁) ⊗ F) ≫ c_{F'}`: multiplication by a section `b` of
`I₂` on a module restricted along `h^♯` is multiplication by `h^♯(b)`, which is the image of `b`
under the induced map of defining ideals. -/
theorem restrictedExtension_actionMap :
    (extensionActionMap D.second (D.restrictedExtension E)).1 =
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F)).map D.idealMap ≫
        (extensionActionMap D.first E).1 := by
  refine extensionActionMap_unique D.second (D.restrictedExtension E) _ ?_
  intro U b x
  let x' : E.Z.left.val.obj U := x
  change E.f.val.app U
      ((extensionActionMap D.first E).1.val.app U
        (((((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F)).map
            D.idealMap).val.app U
          (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
            (PresheafOfModules.tensorObj D.second.I.val F.val)).app U
            (b ⊗ₜ[(baseRing i).obj.obj U] E.g.val.app U x')))) = _
  refine Eq.trans (congrArg
    (fun z => E.f.val.app U ((extensionActionMap D.first E).1.val.app U z))
    (tensorSheaf_map_unit_tmul (baseRing i) (H := F) D.idealMap U b (E.g.val.app U x'))) ?_
  refine ((extensionActionMap D.first E).2 U (D.idealMap.val.app U b) x').trans ?_
  exact congrArg (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U => r • x')
    (D.inclOne_idealMap U b)

end MorphismOfFirstOrderThickenings

end Deformation.ToposThickening

end
