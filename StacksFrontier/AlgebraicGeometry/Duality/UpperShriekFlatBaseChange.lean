module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.FlatBaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition

/-!
# Flat base change for `f^!`

In Situation [Stacks, Tag 0F42] let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of `AlgebraicGeometry.FTS S` with `g` flat, and let `j : X ⟶ X̄`,
`f̄ : X̄ ⟶ Y` be a compactification of `f`. Its base change `X' ⟶ X̄' = X̄ ×_Y Y' ⟶ Y'` is a
compactification of `f'`, and the base change map

`L(g')^* ∘ f^! = L(g')^* ∘ j^* ∘ ā ≅ (j')^* ∘ L(ḡ')^* ∘ ā ⟶ (j')^* ∘ ā' ∘ Lg^* = (f')^! ∘ Lg^*`

whose middle arrow is the base change map of [Stacks, Tag 0AA6] for `X̄' ⟶ X̄` over `Y' ⟶ Y`, is
an isomorphism on `D^+_QCoh(𝒪_Y)`. This is [Stacks, Tag 0E9U]; it is stated here untagged.

## Main definitions

* `Stacks.Duality.baseChangeCompactification` — the compactification `X' ⟶ X̄ ×_Y Y' ⟶ Y'` of
  `f'`.
* `Stacks.Duality.upperShriekBaseChangeMap` — the base change map `L(g')^* ∘ f^! ⟶ (f')^! ∘ Lg^*`.

## Main results

* `Stacks.Duality.isIso_upperShriekBaseChangeMap_app` — it is invertible on `D^+_QCoh(𝒪_Y)`
  for `g` flat.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} {X' X Y' Y : FTS S} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y} (sq : IsPullback g'.left f'.left f.left g.left)
  (c : CompactificationOf (Over.mk f.left))

/-! ### The base change of a compactification -/

include sq in
/-- The maps `X' ⟶ X ⟶ X̄ ⟶ Y` and `X' ⟶ Y' ⟶ Y` agree. -/
theorem baseChangeCompactification_condition :
    (g'.left ≫ c.immersion) ≫ c.toBase = f'.left ≫ g.left := by
  rw [Category.assoc, immersion_comp_toBase f c, sq.w]

/-- The morphism `j' : X' ⟶ X̄ ×_Y Y'` induced by `g' ≫ j` and `f'`. -/
abbrev baseChangeCompactificationImmersion : X'.left ⟶ pullback c.toBase g.left :=
  pullback.lift (g'.left ≫ c.immersion) f'.left (baseChangeCompactification_condition sq c)

/-- **The square `X' ⟶ X̄'` over `X ⟶ X̄` is cartesian**: pasted with the cartesian square
`X̄' ⟶ X̄` over `Y' ⟶ Y` it gives the cartesian square `X'` over `Y'`. -/
theorem isPullback_baseChangeCompactificationImmersion :
    IsPullback (baseChangeCompactificationImmersion sq c) g'.left (pullback.fst c.toBase g.left)
      c.immersion :=
  IsPullback.of_right
    (by rw [pullback.lift_snd, immersion_comp_toBase f c]; exact sq.flip)
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback c.toBase g.left).flip

/-- The morphism `j' : X' ⟶ X̄ ×_Y Y'` is an open immersion. -/
instance isOpenImmersion_baseChangeCompactificationImmersion :
    IsOpenImmersion (baseChangeCompactificationImmersion sq c) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeCompactificationImmersion sq c).flip
    inferInstance

/-- **The base change of a compactification along a cartesian square of `FTS S`**: the open
immersion `X' ⟶ X̄ ×_Y Y'` followed by the proper projection `X̄ ×_Y Y' ⟶ Y'`. -/
def baseChangeCompactification : CompactificationOf (Over.mk f'.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk (pullback.snd c.toBase g.left))
      (Over.homMk (baseChangeCompactificationImmersion sq c) (pullback.lift_snd _ _ _)),
    ⟨(inferInstance : IsOpenImmersion (baseChangeCompactificationImmersion sq c)),
      (inferInstance : IsProper (pullback.snd c.toBase g.left))⟩⟩

/-- The proper map of the base change compactification is the projection `X̄ ×_Y Y' ⟶ Y'`. -/
@[simp]
theorem baseChangeCompactification_toBase :
    (baseChangeCompactification sq c).toBase = pullback.snd c.toBase g.left :=
  rfl

/-- The open immersion of the base change compactification is `j' : X' ⟶ X̄ ×_Y Y'`. -/
@[simp]
theorem baseChangeCompactification_immersion :
    (baseChangeCompactification sq c).immersion = baseChangeCompactificationImmersion sq c :=
  rfl

/-! ### The base change map -/

/-- A transformation `F ≅ A ⋙ H ⟶ B ⋙ H ≅ G` built from `β : A ⟶ B` is invertible at `K` as
soon as `β` is. -/
theorem _root_.CategoryTheory.isIso_app_comp_whiskerRight_comp {C D E : Type*} [Category C]
    [Category D] [Category E] {F G : C ⥤ E} {A B : C ⥤ D} {H : D ⥤ E} (e : F ≅ A ⋙ H)
    (β : A ⟶ B) (e' : B ⋙ H ≅ G) (K : C) [IsIso (β.app K)] :
    IsIso ((e.hom ≫ Functor.whiskerRight β H ≫ e'.hom).app K) := by
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

section Map

variable [CompactSpace S] [QuasiSeparatedSpace S] [Flat g.left]

/-- The projection `X̄' = X̄ ×_Y Y' ⟶ X̄`. -/
abbrev baseChangeCompactificationFst : (baseChangeCompactification sq c).space ⟶ c.space :=
  pullback.fst c.toBase g.left

omit [CompactSpace S] [QuasiSeparatedSpace S] [Flat g.left] in
/-- The square `X̄' ⟶ X̄` over `Y' ⟶ Y` of the base change compactification. -/
theorem isPullback_baseChangeCompactification :
    IsPullback (baseChangeCompactificationFst sq c) (baseChangeCompactification sq c).toBase
      c.toBase g.left :=
  IsPullback.of_hasPullback c.toBase g.left

/-- The base change map `L(ḡ')^* ∘ ā ⟶ ā' ∘ Lg^*` of [Stacks, Tag 0AA6] for the compactified
square, `g` flat. -/
def compactificationBaseChangeMap :
    twistedInverseImage c.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase) ⋙
        quasiCoherentDerivedPullback' (baseChangeCompactificationFst sq c) ⟶
      quasiCoherentDerivedPullback' g.left ⋙
        twistedInverseImage (baseChangeCompactification sq c).toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _) :=
  haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent
    (isPullback_baseChangeCompactification sq c) (torIndependent_of_flat_right c.toBase g.left)
  twistedInverseImageBaseChangeMap _ _ _ _ _ _ _ _ (isPullback_baseChangeCompactification sq c)

omit [CompactSpace S] [QuasiSeparatedSpace S] [Flat g.left] in
/-- The two composites `X' ⟶ X̄' ⟶ X̄` and `X' ⟶ X ⟶ X̄` agree. -/
theorem baseChangeCompactificationImmersion_comp_fst :
    baseChangeCompactificationImmersion sq c ≫ baseChangeCompactificationFst sq c =
      g'.left ≫ c.immersion :=
  pullback.lift_fst _ _ _

/-- The identification `L(g')^* ∘ j^* ∘ ā ≅ (j')^* ∘ L(ḡ')^* ∘ ā` through the equality
`g' ≫ j = j' ≫ ḡ'`. -/
def upperShriekBaseChangePullbackIso :
    upperShriek f c ⋙ quasiCoherentDerivedPullback' g'.left ≅
      (twistedInverseImage c.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase) ⋙
        quasiCoherentDerivedPullback' (baseChangeCompactificationFst sq c)) ⋙
        quasiCoherentDerivedPullback' (baseChangeCompactificationImmersion sq c) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (quasiCoherentDerivedPullbackCompIso g'.left c.immersion ≪≫
      quasiCoherentDerivedPullbackCongr
        (baseChangeCompactificationImmersion_comp_fst sq c).symm ≪≫
      (quasiCoherentDerivedPullbackCompIso (baseChangeCompactificationImmersion sq c)
        (baseChangeCompactificationFst sq c)).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- **The base change map `L(g')^* ∘ f^! ⟶ (f')^! ∘ Lg^*`** of [Stacks, Tag 0E9U], for a
compactification `j` of `f` and its base change `j'`:
`L(g')^* j^* ā ≅ (j')^* L(ḡ')^* ā ⟶ (j')^* ā' Lg^*`, the middle arrow being the base change map
of [Stacks, Tag 0AA6] for the compactified square. -/
def upperShriekBaseChangeMap :
    upperShriek f c ⋙ quasiCoherentDerivedPullback' g'.left ⟶
      quasiCoherentDerivedPullback' g.left ⋙ upperShriek f' (baseChangeCompactification sq c) :=
  (upperShriekBaseChangePullbackIso sq c).hom ≫
    Functor.whiskerRight (compactificationBaseChangeMap sq c)
      (quasiCoherentDerivedPullback' (baseChangeCompactificationImmersion sq c)) ≫
    (Functor.associator _ _ _).hom

/-- **[Stacks, Tag 0E9U]**, untagged. Let `S` be Noetherian and let `X' ⟶ X` over `Y' ⟶ Y` be a
cartesian square of `FTS S` with `g` flat. For every compactification `j` of `f` and its base
change `j'`, the base change map `L(g')^* ∘ f^! ⟶ (f')^! ∘ Lg^*` is an isomorphism on
`D^+_QCoh(𝒪_Y)`. -/
theorem isIso_upperShriekBaseChangeMap_app [IsNoetherian S]
    (K : quasiCoherentDerivedCategory Y.left) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((upperShriekBaseChangeMap sq c).app K) := by
  have : IsIso ((compactificationBaseChangeMap sq c).app K) :=
    isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right
      (isPullback_baseChangeCompactification sq c) K hK
  exact isIso_app_comp_whiskerRight_comp (upperShriekBaseChangePullbackIso sq c)
    (compactificationBaseChangeMap sq c) (Functor.associator _ _ _) K

end Map

end Stacks.Duality

end
