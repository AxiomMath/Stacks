module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordIsomCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCover
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.InertiaFibre

/-!
# The inertia of an algebraic stack through its automorphism group algebraic spaces

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site. The base change of the
forgetful 1-morphism `π : I_𝒳 ⟶ 𝒳` of the inertia along a scheme-valued point `x : U ⟶ 𝒳` is
the automorphism group algebraic space `Isom_𝒳(x, x)` of **Stacks 04YP** over `U`. This file
records the consequences for the properties of `π` in the sense of Properties of Stacks,
Section 04XB (**Stacks 03YK**): for a property tested on étale charts, `π` has it exactly when
every `Isom_𝒳(x, x) ⟶ U` has it, and the same holds for quasi-compactness. Flatness and local
finite presentation of `π` in the sense of **Stacks 06PW** and **Stacks 06Q2** are read through
**Stacks 06FM**.

## Main results

* `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_algebraicSpaceMap_inertia_iff_isomSpace`: at a
  scheme-valued point, a property tested on étale charts holds for the algebraic space
  representing the base change of `π` exactly when it holds for the automorphism space of the
  point.
* `AlgebraicGeometry.Stack.isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection`:
  if `π` is quasi-compact (**Stacks 050U**), every automorphism space is quasi-compact over its
  base.
* `AlgebraicGeometry.Stack.isFlat_inertiaProjection_iff_isomSpace` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_inertiaProjection_iff_isomSpace`: `π` is
  flat, resp. locally of finite presentation, exactly when every automorphism space is.

## Implementation notes

The computation of the base change is `CategoryTheory.TwoFibreProductOver.InertiaFibre`, which
identifies it with the presheaf of vertical automorphisms of the point, and
`CategoryTheory.Functor.vertHomPresheafIsoIsomPresheafOfFunctors`, which identifies that
presheaf with `Isom_𝒳(x, x)` read on the site of `U`. The passage between the property read
over `S` and the property read over `U` is the one of
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_algebraicSpaceMap_iff_isomSpace`, the analogous
statement for the relative diagonal, and for quasi-compactness it is
`AlgebraicGeometry.Space.isQuasiCompact_of_relocalizeMap`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver.InertiaFibre

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The base change of the inertia projection along a scheme-valued point is the automorphism
space of the point.** If an algebraic space `F` over `U` represents the base change of
`π : I_𝒳 ⟶ 𝒳` along a scheme-valued point `y` of `𝒳` over `U`, then `F` is isomorphic to
`Isom_𝒳(x, x)` for `x` the value of `y` at the terminal object. -/
theorem nonempty_iso_isomSpace_of_inertia (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (inertiaAlgebraicStack B S hS 𝒳).val.val.p
        𝒳.val.val.p y
        (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Nonempty (F ≅ isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
      (Functor.sliceValue 𝒳.val.val.p U y hy)) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff (q := 𝟭 _) 𝒳.val.isFiberedInGroupoids
    (Functor.comp_id _) hy F).mp hE
  have hiso : autPresheaf 𝒳.val.isFiberedInGroupoids hy ≅ F :=
    ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e
  exact ⟨hiso.symm ≪≫ Functor.vertHomPresheafIsoIsomPresheafOfFunctors 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids U y y hy hy⟩

/-- **The base change of the inertia projection and the automorphism space have the same
étale-chart properties.** -/
theorem holdsOnEveryEtaleChart_algebraicSpaceMap_inertia_iff_isomSpace
    (P : MorphismProperty Scheme.{u}) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (inertiaAlgebraicStack B S hS 𝒳).val.val.p
        𝒳.val.val.p y
        (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B S hS P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
          (Functor.sliceValue 𝒳.val.val.p U y hy))) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨iI⟩ := nonempty_iso_isomSpace_of_inertia B S hS 𝒳 U y hy F hE
  let Ppre : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.HoldsOnEveryEtaleChart B S hS P g
  have _ : Ppre.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS P
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    Ppre.inverseImage (ObjectProperty.ι _)
  have _ : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  refine (prop_algebraicSpaceMap_iff B S hS Q U F hF).trans ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    P F).trans ?_
  let PU : MorphismProperty ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P g
  have _ : PU.RespectsIso :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf B U.left.1 U.left.2 P
  have hterm : PU (Space.toYonedaId B U.left.1 U.left.2 F) ↔ PU (terminal.from F) :=
    ⟨fun h => Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2
      (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _ h,
     fun h => Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2
      terminalIsTerminal (Over.mkIdTerminal.isTerminalObj yoneda _) _ _ h⟩
  refine hterm.trans ?_
  rw [show terminal.from F = iI.hom ≫ terminal.from _ from terminal.hom_ext _ _]
  exact PU.cancel_left_of_respectsIso iI.hom _

/-- The tautological scheme-valued point of `𝒳` attached to an object `x` over `U`, together with
the identification of the automorphism space at its value with that of `x`. -/
theorem holdsOnEveryEtaleChart_isomSpace_sliceValue_pullback_iff (P : MorphismProperty Scheme.{u})
    (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U
          (Functor.sliceValue 𝒳.val.val.p U
            (Over.iteratedSliceBackward U ⋙ Functor.pullbackSliceFunctor 𝒳.val.val.p x)
            (Functor.backward_pullbackSliceFunctor_comp 𝒳.val.val.p U x))
          (Functor.sliceValue 𝒳.val.val.p U
            (Over.iteratedSliceBackward U ⋙ Functor.pullbackSliceFunctor 𝒳.val.val.p x)
            (Functor.backward_pullbackSliceFunctor_comp 𝒳.val.val.p U x)))) ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U x x)) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let p := 𝒳.val.val.p
  let W := Over.iteratedSliceBackward U ⋙ Functor.pullbackSliceFunctor p x
  have hW : W ⋙ p = Over.map U.hom := Functor.backward_pullbackSliceFunctor_comp p U x
  let g := Functor.structHom U (Over.mk (𝟙 U.left))
  let e : U ⟶ U := eqToHom (Functor.overMap_obj_mkId U).symm ≫ g
  have he : e = 𝟙 U := by
    ext
    simp [e, g]
  have _ : IsIso e := by
    rw [he]
    infer_instance
  let m : (Functor.sliceValue p U W hW).1 ⟶ x.1 :=
    Functor.IsPreFibered.pullbackMap x.2 g
  have hlift : p.IsHomLift e m := by
    have : p.IsCartesian g m := Functor.IsPreFibered.pullbackMap.IsCartesian (p := p) x.2 g
    refine IsHomLift.of_fac' p e m (Functor.sliceValue p U W hW).2 x.2 ?_
    rw [IsHomLift.fac' p g m]
    simp [e]
  exact holdsOnEveryEtaleChart_isomSpace_iff_of_isIso B S hS P 𝒳.val e m
    (𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift e m)

/-- The automorphism space of the value of a scheme-valued point represents the base change of the
inertia projection along that point. -/
private theorem nonempty_equivalenceOver_inertia_isomSpace (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (inertiaAlgebraicStack B S hS 𝒳).val.val.p
        𝒳.val.val.p y
        (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
      (presheafOfCategories
        (isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
          (Functor.sliceValue 𝒳.val.val.p U y hy) ⋙ typeToCat)).p) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  exact (nonempty_equivalenceOver_fst_iff (q := 𝟭 _) 𝒳.val.isFiberedInGroupoids
    (Functor.comp_id _) hy _).mpr
    ⟨Functor.isoWhiskerRight (Functor.vertHomPresheafIsoIsomPresheafOfFunctors 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids U y y hy hy) uliftFunctor.{u, u}⟩

/-- **The automorphism spaces of `𝒳` have every étale-chart property the inertia projection
has.** -/
theorem holdsOnEveryEtaleChart_isomSpace_of_inertia (P : MorphismProperty Scheme.{u})
    (h : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) (inertiaAlgebraicStack B S hS 𝒳).val.val.p
          𝒳.val.val.p y
          (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.HoldsOnEveryEtaleChart B S hS P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
      (terminal.from (isomSpace B S hS 𝒳.val U x x)) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let p := 𝒳.val.val.p
  let W := Over.iteratedSliceBackward U ⋙ Functor.pullbackSliceFunctor p x
  have hW : W ⋙ p = Over.map U.hom := Functor.backward_pullbackSliceFunctor_comp p U x
  let I := isomSpace B S hS 𝒳.val U (Functor.sliceValue p U W hW)
    (Functor.sliceValue p U W hW)
  have hI : IsAlgebraicSpace B U.left.1 U.left.2 I :=
    isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property U _ _
  have hE := nonempty_equivalenceOver_inertia_isomSpace B S hS 𝒳 U W hW
  exact (holdsOnEveryEtaleChart_isomSpace_sliceValue_pullback_iff B S hS 𝒳 P U x).mp
    ((holdsOnEveryEtaleChart_algebraicSpaceMap_inertia_iff_isomSpace B S hS 𝒳 P U W
      hW I hI hE).mp (h U W hW I hI hE))

/-- **The inertia projection has every étale-chart property its automorphism spaces have.** -/
theorem inertia_of_holdsOnEveryEtaleChart_isomSpace (P : MorphismProperty Scheme.{u})
    (hx : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U x x)))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (inertiaAlgebraicStack B S hS 𝒳).val.val.p
        𝒳.val.val.p y
        (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Space.HoldsOnEveryEtaleChart B S hS P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  (holdsOnEveryEtaleChart_algebraicSpaceMap_inertia_iff_isomSpace B S hS 𝒳 P U y hy F hF hE).mpr
    (hx U _)

/-- **A quasi-compact inertia projection has quasi-compact automorphism spaces.** If the
inertia projection `π : I_𝒳 ⟶ 𝒳` is quasi-compact in the sense of **Stacks 050U**, then for every
scheme-valued point `y` of `𝒳` over `U` the automorphism space of its value at the terminal object
is quasi-compact over `U`.

By **Stacks 050T** the hypothesis is the relative quasi-compactness of `π`; at the point `y` the
representing algebraic space is the automorphism space, and quasi-compactness of its structural
morphism read over `S` descends to the one read over `U` by
`AlgebraicGeometry.Space.isQuasiCompact_of_relocalizeMap`. -/
theorem isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.IsQuasiCompact B U.left.1 U.left.2
      (terminal.from (isomSpace B S hS 𝒳.val U (Functor.sliceValue 𝒳.val.val.p U y hy)
        (Functor.sliceValue 𝒳.val.val.p U y hy))) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have hrep :=
    isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
    B S hS 𝒳.val 𝒳.property
  have hrel : IsQuasiCompact B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom :=
    (isQuasiCompact_iff_baseChange_quasiCompact B S hS
      (inertiaProjectionAlgebraicStacks B S hS 𝒳) hrep).2 hqc
  let p := 𝒳.val.val.p
  let I := isomSpace B S hS 𝒳.val U (Functor.sliceValue p U y hy) (Functor.sliceValue p U y hy)
  have hI : IsAlgebraicSpace B U.left.1 U.left.2 I :=
    isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property U _ _
  have hE := nonempty_equivalenceOver_inertia_isomSpace B S hS 𝒳 U y hy
  have hiso : (Space.quasiCompactProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h₁ := (prop_algebraicSpaceMap_iff B S hS (Space.quasiCompactProperty B S hS) U I hI).1
    (hrel U y hy I hI hE)
  change Space.IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda U.hom I) at h₁
  have hisoP : (Space.quasiCompactPresheafProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ := isIso_relocalizeToYoneda_yonedaId B U.left.1 S U.left.2 hS U.hom
  rw [← relocalizeToYoneda_eq_map_toYonedaId B U.left.1 S U.left.2 hS U.hom I] at h₁
  have h₂ : Space.IsQuasiCompact B S hS
      ((OverShriek.relocalizePresheafFunctor U.hom).map (Space.toYonedaId B U.left.1 U.left.2 I)) :=
    (MorphismProperty.cancel_right_of_respectsIso (Space.quasiCompactPresheafProperty B S hS)
      _ (OverShriek.relocalizeToYoneda U.hom (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2)))))).1 h₁
  have hisoU : (Space.quasiCompactPresheafProperty B U.left.1 U.left.2).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let t : yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))) ≅ ⊤_ _ :=
    (Over.mkIdTerminal.isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal
  rw [show terminal.from I = Space.toYonedaId B U.left.1 U.left.2 I ≫ t.hom from
    terminal.hom_ext _ _]
  exact (MorphismProperty.cancel_right_of_respectsIso
    (Space.quasiCompactPresheafProperty B U.left.1 U.left.2) _ t.hom).2
    (Space.isQuasiCompact_of_relocalizeMap B U.left.1 S U.left.2 hS U.hom _ h₂)

section FlatLfp

/-- **The inertia projection is flat exactly when every automorphism space is.** Flatness of a
1-morphism of algebraic stacks (**Stacks 06PW**) is, for the inertia projection, which is
representable by algebraic spaces (**Stacks 050Q**), the relative flatness of **Stacks 03YK** by
**Stacks 06FM**; and that is flatness of every automorphism space. -/
theorem isFlat_inertiaProjection_iff_isomSpace :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) ↔
      ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
        Space.IsFlat B U.left.1 U.left.2 (terminal.from (isomSpace B S hS 𝒳.val U x x)) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have _ : (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hrep :=
    isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
    B S hS 𝒳.val 𝒳.property
  exact (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) (inertiaAlgebraicStack B S hS 𝒳).property
    𝒳.property (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom hrep).trans
      ⟨fun h => holdsOnEveryEtaleChart_isomSpace_of_inertia B S hS 𝒳 _ h,
        inertia_of_holdsOnEveryEtaleChart_isomSpace B S hS 𝒳 _⟩

/-- **The inertia projection is locally of finite presentation exactly when every automorphism
space is.** Local finite presentation of a 1-morphism of algebraic stacks (**Stacks 06Q2**) is
the universal smooth-diagram test, which for the representable inertia projection is the relative
property of **Stacks 03YK** by **Stacks 06FM**. -/
theorem isLocallyOfFinitePresentation_inertiaProjection_iff_isomSpace :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒳) ↔
      ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
        Space.IsLocallyOfFinitePresentation B U.left.1 U.left.2
          (terminal.from (isomSpace B S hS 𝒳.val U x x)) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have hrep :=
    isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
    B S hS 𝒳.val 𝒳.property
  exact (hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (inertiaAlgebraicStack B S hS 𝒳).property
    𝒳.property (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom hrep).trans
      ⟨fun h => holdsOnEveryEtaleChart_isomSpace_of_inertia B S hS 𝒳 _ h,
        inertia_of_holdsOnEveryEtaleChart_isomSpace B S hS 𝒳 _⟩

end FlatLfp

end AlgebraicGeometry.Stack

end
