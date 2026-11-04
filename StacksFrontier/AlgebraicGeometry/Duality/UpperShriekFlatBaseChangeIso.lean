module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFlatBaseChange

/-!
# Flat base change for `f^!` on `D^+_QCoh`

In Situation [Stacks, Tag 0F42] let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of `AlgebraicGeometry.FTS S` with `g` flat. Then
`L(g')^* ∘ f^! ≅ (f')^! ∘ Lg^*` on `D^+_QCoh(𝒪_Y)` ([Stacks, Tag 0E9U]). For a compactification
`j` of `f` and its base change `j'`, the base change map `L(g')^* ∘ f^! ⟶ (f')^! ∘ Lg^*`
(`Stacks.Duality.upperShriekBaseChangeMap`) is invertible on `D^+_QCoh(𝒪_Y)`; composing with the
comparison of [Stacks, Tag 0AA0] between compactifications of `f'` computes `(f')^!` at any
compactification of `f'`.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedPullbackPlusOfFlat` —
  `Lg^* : D^+_QCoh(𝒪_Y) ⥤ D^+_QCoh(𝒪_{Y'})` for `g` flat.
* `Stacks.Duality.upperShriekBaseChangePlusIso` — the base change map as an isomorphism on
  `D^+_QCoh(𝒪_Y)`.
* `Stacks.Duality.upperShriekFlatBaseChangeIso` — [Stacks, Tag 0E9U].

## References

* [Stacks Project, Tag 0E9U](https://stacks.math.columbia.edu/tag/0E9U)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **Derived pullback along a flat morphism on `D^+_QCoh`**: for `e : Z ⟶ W` flat, `Le^*`
carries `D^+_QCoh(𝒪_W)` into `D^+_QCoh(𝒪_Z)`. -/
def quasiCoherentDerivedPullbackPlusOfFlat {Z W : Scheme.{u}} (e : Z ⟶ W) [Flat e] :
    quasiCoherentDerivedCategoryPlusOfModel W ⥤ quasiCoherentDerivedCategoryPlusOfModel Z :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ quasiCoherentDerivedPullback' e)
    fun K => isBoundedBelow_quasiCoherentDerivedPullback_obj_of_flat e K.obj K.property

variable {S : Scheme.{u}} [IsNoetherian S] {X' X Y' Y : FTS S} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} [Flat g.left] (sq : IsPullback g'.left f'.left f.left g.left)
  (c : CompactificationOf (Over.mk f.left))

/-- **The base change map `L(g')^* ∘ f^! ≅ (f')^! ∘ Lg^*` as an isomorphism on `D^+_QCoh(𝒪_Y)`**,
with `f^!` computed at a compactification `j` of `f` and `(f')^!` at its base change `j'`. -/
def upperShriekBaseChangePlusIso :
    (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        upperShriek f c ⋙ quasiCoherentDerivedPullback' g'.left ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' g.left ⋙ upperShriek f' (baseChangeCompactification sq c) :=
  NatIso.ofComponents
    (fun K => @asIso _ _ _ _ ((upperShriekBaseChangeMap sq c).app K.obj)
      (isIso_upperShriekBaseChangeMap_app sq c K.obj K.property))
    (fun h => (upperShriekBaseChangeMap sq c).naturality
      ((ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _).map h))

/-- The component of `upperShriekBaseChangePlusIso sq c` at `K` is the component of the base
change map `upperShriekBaseChangeMap sq c` at the underlying complex of `K`. -/
@[simp]
theorem upperShriekBaseChangePlusIso_hom_app (K : quasiCoherentDerivedCategoryPlusOfModel Y.left) :
    (upperShriekBaseChangePlusIso sq c).hom.app K = (upperShriekBaseChangeMap sq c).app K.obj :=
  rfl

/-- **Flat base change for `f^!`.** Let `S` be Noetherian and let `X' ⟶ X` over `Y' ⟶ Y` be a
cartesian square of `FTS S` with `g` flat. Then `L(g')^* ∘ f^! ≅ (f')^! ∘ Lg^*` on
`D^+_QCoh(𝒪_Y)`, with `f^!` computed at any compactification `j` of `f` and `(f')^!` at any
compactification `c'` of `f'`. It is the base change map `L(g')^* j^* ā ≅ (j')^* L(ḡ')^* ā ⟶
(j')^* ā' Lg^*` of the base change `j'` of `j`, followed by the comparison
`(f')^!_{j'} ≅ (f')^!_{c'}` of [Stacks, Tag 0AA0] at `Lg^*K ∈ D^+_QCoh(𝒪_{Y'})`. -/
@[stacks 0E9U]
def upperShriekFlatBaseChangeIso (c' : CompactificationOf (Over.mk f'.left)) :
    (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        upperShriek f c ⋙ quasiCoherentDerivedPullback' g'.left ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        quasiCoherentDerivedPullback' g.left ⋙ upperShriek f' c' :=
  upperShriekBaseChangePlusIso sq c ≪≫
    Functor.isoWhiskerLeft (quasiCoherentDerivedPullbackPlusOfFlat g.left)
      (Functor.isoWhiskerRight
        (DominatingCompactification.upperShriekPlusIso f' (baseChangeCompactification sq c) c')
        (ObjectProperty.ι _))

end Stacks.Duality

end
