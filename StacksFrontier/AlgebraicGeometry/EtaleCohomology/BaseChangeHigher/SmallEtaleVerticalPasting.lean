module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting

/-!
# Pasting of the base change map of abelian small étale sheaves along the direct image legs

Let

```
Y --h'--> X'' --π'--> X'
|e         |f''        |f'
v          v           v
T --g'--> S'' --π-->  S'
```

be two commutative squares of schemes sharing the edge `f''`, so that `h' ≫ f'' = e ≫ g'` and
`π' ≫ f' = f'' ≫ π`. The outer rectangle commutes as well, and this file proves that the base
change map of the outer rectangle is the composite of the base change maps of the two squares,
read through the composition comparisons for the *direct images* along the two composite legs
`g' ≫ π` and `h' ≫ π'` — the pasting law along the direct image legs, as opposed to
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_paste`, which composes two squares along the
inverse image legs with the direct images fixed.

Both laws are proved the same way: the base change map is the mate of the identification of the
two composite direct images around the square, pasting of mates is Mathlib's
`CategoryTheory.mateEquiv_vcomp` — here for the *horizontal* composition of 2-squares, where
there it was the vertical one — and the geometric content is a cancellation of three instances
of the associativity pentagon `Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_assoc`,
applied to the threefold composites `(e, g', π)`, `(h', f'', π)` and `(h', π', f')` through the
rectangle.

Its descent to the bounded below derived categories is
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleVRectangle_comm`: the outer rectangle commutes.
* `Stacks.EtaleCohomology.mateEquiv_whiskerTop_whiskerBottom`: **the mates equivalence is
  natural in the two vertical legs of the square**, which is what lets the comparisons of the
  composite direct images be moved across it.
* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso_vpaste_app`: the pasting of the square
  comparisons of direct images, the geometric content.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_vpaste` and
  `..._vpaste_app`: **the underived pasting law along the direct image legs**, as an identity of
  2-squares and evaluated at a sheaf.

## Implementation notes

*No tag is placed.* [Stacks, Tag 0E46] states this pasting law for ringed topoi and the derived
base change map of Remark 21.19.3 on unbounded derived categories of complexes of modules; that
statement is already carried, by
`Stacks.Cohomology.DerivedBaseChangePasting.derivedBaseChangeMap_comp`. What is proved here is
the same assertion in a different setting — abelian sheaves on the small étale sites of schemes,
on bounded below derived categories — and not a further part of the source's text, so it is left
untagged.

*The cancellation is the same as for the inverse image legs.*
`Stacks.EtaleCohomology.paste_algebra`, reused from the inverse-image-leg law, is the
identical rearrangement of fourteen
morphisms that the inverse-image-leg law uses; the two configurations differ in which
comparisons are inverted and in which of them are in the image of a direct image functor, not in
the shape of the cancellation.

*Why the exactness hypotheses are instance arguments.* The derived law needs the direct images
along `π` and `π'` to be exact, which for the intended application holds because `π` is integral
and `π'` is its base change; integrality is not visible here, so the four preservation
properties are instance arguments and the consumer supplies them.

## References

* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The mates equivalence is natural in the two vertical legs -/

section MateWhisker

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  {G G₀ : C₁ ⥤ C₃} {H H₀ : C₂ ⥤ C₄}
  {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- **The mates equivalence is natural in the two vertical legs of the square.** Whiskering a
2-square at the top by `α : G₀ ⟶ G` and at the bottom by `β : H ⟶ H₀` whiskers its mate on the
right by `α` and on the left by `β`. Only the naturality of the unit of the lower adjunction and
of `β` is used. -/
theorem mateEquiv_whiskerTop_whiskerBottom (w : TwoSquare G L₁ L₂ H) (α : G₀ ⟶ G) (β : H ⟶ H₀) :
    mateEquiv adj₁ adj₂ ((w.whiskerTop α).whiskerBottom β) =
      ((mateEquiv adj₁ adj₂ w).whiskerRight α).whiskerLeft β := by
  refine TwoSquare.ext _ _ fun d => ?_
  have h₁ : adj₂.unit.app (G₀.obj (R₁.obj d)) ≫ R₂.map (L₂.map (α.app (R₁.obj d))) =
      α.app (R₁.obj d) ≫ adj₂.unit.app (G.obj (R₁.obj d)) := by
    simp
  have h₂ : R₂.map (β.app (L₁.obj (R₁.obj d))) ≫ R₂.map (H₀.map (adj₁.counit.app d)) =
      R₂.map (H.map (adj₁.counit.app d)) ≫ R₂.map (β.app d) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg R₂.map (β.naturality (adj₁.counit.app d)).symm
  dsimp [mateEquiv, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight]
  simp only [Category.assoc, Category.id_comp, Category.comp_id, Functor.map_comp]
  rw [reassoc_of% h₁, h₂]

end MateWhisker

/-! ### The rectangle, and the cancellation -/

section VPaste

variable {X' X'' S' S'' Y T : Scheme.{u}} (f' : X' ⟶ S') (π : S'' ⟶ S') (π' : X'' ⟶ X')
  (f'' : X'' ⟶ S'') (g' : T ⟶ S'') (h' : Y ⟶ X'') (e : Y ⟶ T)
  (w₂ : π' ≫ f' = f'' ≫ π) (w₃ : h' ≫ f'' = e ≫ g')

include w₂ w₃ in
/-- **The outer rectangle of two commutative squares composed along the direct image legs
commutes.** -/
theorem smallEtaleVRectangle_comm : (h' ≫ π') ≫ f' = e ≫ g' ≫ π := by
  rw [Category.assoc, w₂, reassoc_of% w₃]

/-- **The pasting of the square comparisons of direct images along the direct image legs**, which
is the geometric content of the pasting law. The comparison of the two composite direct images
around the outer rectangle is the composite of the comparisons of the two squares, read through
the comparisons of the direct images along the two composite legs. -/
theorem smallEtaleSquarePushforwardIso_vpaste_app
    (𝓖 : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtaleSquarePushforwardIso f' (g' ≫ π) (h' ≫ π') e
          (smallEtaleVRectangle_comm f' π π' f'' g' h' e w₂ w₃)).hom.app 𝓖 =
      (smallEtalePushforwardAbComp' g' π (g' ≫ π) rfl).inv.app
          ((smallEtalePushforwardAb e).obj 𝓖) ≫
        (smallEtalePushforwardAb π).map
            ((smallEtaleSquarePushforwardIso f'' g' h' e w₃).hom.app 𝓖) ≫
          (smallEtaleSquarePushforwardIso f' π π' f'' w₂).hom.app
              ((smallEtalePushforwardAb h').obj 𝓖) ≫
            (smallEtalePushforwardAb f').map
              ((smallEtalePushforwardAbComp' h' π' (h' ≫ π') rfl).hom.app 𝓖) := by
  have hD1 : (h' ≫ π') ≫ f' = (h' ≫ f'') ≫ π := by rw [Category.assoc, w₂, Category.assoc]
  have hD3 : (h' ≫ π') ≫ f' = h' ≫ π' ≫ f' := Category.assoc _ _ _
  have hP₁ := smallEtalePushforwardAbComp'_assoc_app e g' π (h' ≫ f'') w₃ (g' ≫ π) rfl
    ((h' ≫ π') ≫ f') hD1 (smallEtaleVRectangle_comm f' π π' f'' g' h' e w₂ w₃) 𝓖
  have hP₂ := smallEtalePushforwardAbComp'_assoc_app h' f'' π (h' ≫ f'') rfl (π' ≫ f') w₂
    ((h' ≫ π') ≫ f') hD1 hD3 𝓖
  have hP₃ := smallEtalePushforwardAbComp'_assoc_app h' π' f' (h' ≫ π') rfl (π' ≫ f') rfl
    ((h' ≫ π') ≫ f') rfl hD3 𝓖
  simp only [smallEtaleSquarePushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  refine paste_algebra ?_ ?_ ?_ ?_ hP₁.symm hP₂.symm hP₃.symm
  · exact Iso.inv_hom_id_app _ _
  · exact Iso.hom_inv_id_app _ _
  · rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  · exact Iso.inv_hom_id_app _ _

include w₂ w₃ in
/-- **The underived pasting law along the direct image legs.** The base change map of the outer
rectangle is the composite of the base change maps of the two squares, read through the
comparisons of the direct images along the two composite legs `g' ≫ π` and `h' ≫ π'`.

The hypotheses are the commutativity of the two squares and nothing else: neither need be
cartesian, and no finiteness, separatedness or integrality condition enters. -/
theorem smallEtaleBaseChangeAb_vpaste :
    TwoSquare.mk _ _ _ _
        (smallEtaleBaseChangeAb f' (g' ≫ π) (h' ≫ π') e
          (smallEtaleVRectangle_comm f' π π' f'' g' h' e w₂ w₃)) =
      (((TwoSquare.mk _ _ _ _ (smallEtaleBaseChangeAb f'' g' h' e w₃)).hComp
            (TwoSquare.mk _ _ _ _ (smallEtaleBaseChangeAb f' π π' f'' w₂))).whiskerTop
          (smallEtalePushforwardAbCompIso g' π).inv).whiskerBottom
        (smallEtalePushforwardAbCompIso h' π').hom := by
  apply (mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')).injective
  rw [mateEquiv_whiskerTop_whiskerBottom,
    mateEquiv_vcomp (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f'')
      (smallEtaleAdjunctionAb f'),
    mateEquiv_smallEtaleBaseChangeAb, mateEquiv_smallEtaleBaseChangeAb,
    mateEquiv_smallEtaleBaseChangeAb, ← smallEtalePushforwardAbComp'_rfl g' π,
    ← smallEtalePushforwardAbComp'_rfl h' π']
  refine TwoSquare.ext _ _ fun 𝓖 => ?_
  simpa using smallEtaleSquarePushforwardIso_vpaste_app f' π π' f'' g' h' e w₂ w₃ 𝓖

include w₂ w₃ in
/-- **The underived pasting law along the direct image legs, evaluated at a sheaf.** -/
theorem smallEtaleBaseChangeAb_vpaste_app (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtaleBaseChangeAb f' (g' ≫ π) (h' ≫ π') e
          (smallEtaleVRectangle_comm f' π π' f'' g' h' e w₂ w₃)).app F =
      (smallEtalePullbackAb f').map ((smallEtalePushforwardAbCompIso g' π).inv.app F) ≫
        (smallEtaleBaseChangeAb f' π π' f'' w₂).app
            ((smallEtalePushforwardAb g').obj F) ≫
          (smallEtalePushforwardAb π').map
              ((smallEtaleBaseChangeAb f'' g' h' e w₃).app F) ≫
            (smallEtalePushforwardAbCompIso h' π').hom.app
              ((smallEtalePullbackAb e).obj F) := by
  simpa using congr_app (smallEtaleBaseChangeAb_vpaste f' π π' f'' g' h' e w₂ w₃) F

end VPaste

end Stacks.EtaleCohomology

end
