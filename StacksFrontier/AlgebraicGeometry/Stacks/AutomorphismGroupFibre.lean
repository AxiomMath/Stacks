module

public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Properties of the diagonal and of the inertia read on an automorphism group space

For an algebraic stack `𝒳` over `S` and an object `x` of `𝒳` over a scheme `U`, the algebraic
space `Isom_𝒳(x, x)` over `U` is the base change of the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` along `(x, x)`
and the base change of the inertia projection `I_𝒳 ⟶ 𝒳` along `x`. So a property of either
1-morphism in the sense of Properties of Stacks, Section 04XB, holds for `Isom_𝒳(x, x) ⟶ U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
  (x : 𝒳.val.val.p.Fiber U)

/-! ### The automorphism space as a fibre of the diagonal and of the inertia projection -/

section Fibre

/-- The scheme-valued point of `𝒳` over `U` attached to the object `x`: the 1-morphism from the
big fppf site of `U` sending `V ⟶ U` to the chosen pullback of `x` to `V`
(`CategoryTheory.Functor.pullbackSliceFunctor`, read on the site of `U`). -/
noncomputable abbrev isomSpacePoint : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj :=
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  Over.iteratedSliceBackward U ⋙ Functor.pullbackSliceFunctor 𝒳.val.val.p x

/-- The point `AlgebraicGeometry.Stack.isomSpacePoint` lies over the structure morphism of `U`. -/
theorem isomSpacePoint_comp :
    isomSpacePoint B S hS 𝒳 U x ⋙ 𝒳.val.val.p = Over.map U.hom :=
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  Functor.backward_pullbackSliceFunctor_comp 𝒳.val.val.p U x

/-- The point `(x, x)` of `𝒳 × 𝒳`, the image of `AlgebraicGeometry.Stack.isomSpacePoint` under
the diagonal, lies over the structure morphism of `U`. -/
theorem isomSpacePoint_comp_diagonal_comp :
    (isomSpacePoint B S hS 𝒳 U x ⋙
        CatFiberedInGroupoids.homFunctor (diagonal.{u, u, u + 1} B S hS 𝒳.val)) ⋙
      (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p = Over.map U.hom :=
  (congrArg (isomSpacePoint B S hS 𝒳 U x ⋙ ·) (diagonal.{u, u, u + 1} B S hS 𝒳.val).hom.w).trans
    (isomSpacePoint_comp B S hS 𝒳 U x)

/-- **`Isom_𝒳(x, x)` is the fibre of the diagonal at `(x, x)`.** The base change of
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` along the point `(x, x)` of `𝒳 × 𝒳` over `U` is equivalent, over the big fppf
site of `U`, to the category of elements of `Isom_𝒳(x, x)`: the presheaf of vertical morphisms
between the two components of that point is the presheaf of vertical morphisms between the chosen
pullbacks of `x`, which is `Isom_𝒳(x, x)`. -/
theorem nonempty_equivalenceOver_diagonal_isomSpace :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
        (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p
        (isomSpacePoint B S hS 𝒳 U x ⋙
          CatFiberedInGroupoids.homFunctor (diagonal.{u, u, u + 1} B S hS 𝒳.val))
        (CatFiberedInGroupoids.homFunctor (diagonal.{u, u, u + 1} B S hS 𝒳.val)))
      (presheafOfCategories (isomSpace B S hS 𝒳.val U x x ⋙ typeToCat)).p) := by
  have hp := 𝒳.val.isFiberedInGroupoids
  have : 𝒳.val.val.p.IsFibered := hp.isFibered
  exact (TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff hp
    (isomSpacePoint_comp_diagonal_comp B S hS 𝒳 U x) _).2
    ⟨Functor.isoWhiskerRight (Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.val.p U x x hp)
      uliftFunctor.{u, u}⟩

/-- **A relative property of the diagonal is read on `Isom_𝒳(x, x)`.** If the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` satisfies the condition of Properties of Stacks, Section 04XB for a property `P`
of morphisms of algebraic spaces over `S`, then `P` holds for the structural morphism of
`Isom_𝒳(x, x)`, read over `S` by Stacks 04SG: that algebraic space represents the base change of
`Δ` along the point `(x, x)` of `𝒳 × 𝒳`. -/
theorem prop_isomSpace_of_diagonal (P : MorphismProperty (AlgebraicSpaces B S hS))
    (h : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.obj)
      (_hy : y ⋙ (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (CatFiberedInGroupoids.product 𝒳.val 𝒳.val).val.p y
            (CatFiberedInGroupoids.homFunctor (diagonal.{u, u, u + 1} B S hS 𝒳.val)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
        ⟨isomSpace B S hS 𝒳.val U x x,
          isAlgebraicSpace_isomSpace.{u, w} B S hS 𝒳.val 𝒳.property U x x⟩)) :=
  h U _ (isomSpacePoint_comp_diagonal_comp B S hS 𝒳 U x) _ _
    (nonempty_equivalenceOver_diagonal_isomSpace B S hS 𝒳 U x)

/-- **A relative property of the inertia projection is read on `Isom_𝒳(x, x)`.** If the inertia
projection `π : I_𝒳 ⟶ 𝒳` satisfies the condition of Properties of Stacks, Section 04XB for a
property `P` of morphisms of algebraic spaces over `S`, then `P` holds for the structural
morphism of `Isom_𝒳(x, x)`, read over `S` by Stacks 04SG.

By Stacks 034H (1), `I_𝒳` is equivalent over the site to the 2-fibre product
`𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` by a comparison under which `π` is the first projection; so Stacks 0457
carries the condition to that projection. Its base change along the point of `𝒳` attached to `x`
is the base change of `Δ` along `(x, x)`
(`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`), which is the category of elements
of `Isom_𝒳(x, x)`. -/
theorem prop_isomSpace_of_inertiaProjection (P : MorphismProperty (AlgebraicSpaces B S hS))
    (h : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) (inertia B S hS 𝒳.val).val.p 𝒳.val.val.p y
            (CatFiberedInGroupoids.homFunctor (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
        ⟨isomSpace B S hS 𝒳.val U x x,
          isAlgebraicSpace_isomSpace.{u, w} B S hS 𝒳.val 𝒳.property U x x⟩)) := by
  have hG : 𝒳.val.val.p ⋙ 𝟭 (BigFppfOver B S hS) = 𝒳.val.val.p := Functor.comp_id _
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (diagonal.{u, u, u + 1} B S hS 𝒳.val) (diagonal.{u, u, u + 1} B S hS 𝒳.val)
  let aFun : Q.pt.val ⥤ᵇ (inertia B S hS 𝒳.val).val :=
    ⟨TwoFibreProductOver.toRelativeInertia hG,
      TwoFibreProductOver.toRelativeInertia_comp_relativeInertiaStruct hG⟩
  have : Functor.IsEquivalence aFun.toFunctor :=
    TwoFibreProductOver.isEquivalence_toRelativeInertia hG
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  have h₁ := relativeProperty_of_equivalences B S hS P Q.fst.hom
    (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom.hom aFun (BasedFunctor.id 𝒳.val.val)
    (Iso.refl _) h
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, u, u + 1} B S hS 𝒳.val
    (CatFiberedInGroupoids.product 𝒳.val 𝒳.val) 𝒳.val
    (diagonal.{u, u, u + 1} B S hS 𝒳.val) (diagonal.{u, u, u + 1} B S hS 𝒳.val) Q
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    U (isomSpacePoint B S hS 𝒳 U x) (isomSpacePoint_comp B S hS 𝒳 U x)
  obtain ⟨E'⟩ := nonempty_equivalenceOver_diagonal_isomSpace B S hS 𝒳 U x
  exact h₁ U _ (isomSpacePoint_comp B S hS 𝒳 U x) _ _ ⟨E.trans E'⟩

end Fibre

/-! ### Reading a property of the representing space over `U` -/

section ReadOverU

variable {B S hS} {U}

/-- **Quasi-separatedness of the representing space, read over `U`.** If the structural morphism
of an algebraic space `F` over `U`, viewed over `S` by Stacks 04SG, is quasi-separated, then `F`
is quasi-separated over `U`. The structural morphism is the lower-shriek extension of
`F ⟶ U`, whose quasi-separatedness does not depend on the base, and over `U` it is a morphism to
a terminal presheaf, whose relative diagonal is the absolute diagonal of `F`. -/
theorem isQuasiSeparatedOver_of_algebraicSpaceMap
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (h : Space.IsQuasiSeparated B S hS (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    Space.IsQuasiSeparatedOver B U.left.1 U.left.2 F := by
  have : (Space.quasiSeparatedProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h₁ : Space.IsQuasiSeparated B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.quasiSeparatedProperty B S hS) U F hF).mp h
  have h₂ := (Space.isQuasiSeparated_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom F).mp h₁
  exact (Space.isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal B U.left.1
    U.left.2 (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2) _).2
    (Space.diagonalProp_quasiCompact_of_isQuasiSeparated B U.left.1 U.left.2
      (relativelyRepresentable_pullbackDiagonal B U.left.1 U.left.2
        (Space.toYonedaId B U.left.1 U.left.2 F) hF) h₂)

/-- **Local separatedness of the representing space, read over `U`.** If the structural morphism
of an algebraic space `F` over `U`, viewed over `S` by Stacks 04SG, is locally separated, then `F`
is locally separated over `U`. -/
theorem isLocallySeparatedOver_of_algebraicSpaceMap
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (h : Space.IsLocallySeparated B S hS (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    Space.IsLocallySeparatedOver B U.left.1 U.left.2 F := by
  have : (Space.locallySeparatedMorphismProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h₁ : Space.IsLocallySeparated B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.locallySeparatedMorphismProperty B S hS) U F hF).mp h
  have hι : IsIso (OverShriek.relocalizeToYoneda U.hom
      (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))) :=
    isIso_relocalizeToYoneda_yonedaId B U.left.1 S U.left.2 hS U.hom
  have hq : (OverShriek.relocalizePresheafFunctor U.hom).map
        (Space.toYonedaId B U.left.1 U.left.2 F)
      = OverShriek.relocalizeToYoneda U.hom F ≫ inv (OverShriek.relocalizeToYoneda U.hom
        (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))) := by
    rw [← relocalizeToYoneda_eq_map_toYonedaId B U.left.1 S U.left.2 hS U.hom F, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have h₂ : Space.IsLocallySeparated B S hS ((OverShriek.relocalizePresheafFunctor U.hom).map
      (Space.toYonedaId B U.left.1 U.left.2 F)) := by
    rw [hq]
    exact Space.isLocallySeparated_comp B S hS _ _ h₁ (Space.isLocallySeparated_of_isIso B S hS _)
  have h₃ := Space.isLocallySeparated_of_relocalize B U.left.1 U.left.2 hS U.hom
    (relativelyRepresentable_pullbackDiagonal B U.left.1 U.left.2
      (Space.toYonedaId B U.left.1 U.left.2 F) hF) h₂
  exact (Space.isLocallySeparatedOver_iff_isLocallySeparated_of_isTerminal B U.left.1 U.left.2
    (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2) _).2 h₃

/-- **Local quasi-finiteness of the representing space, read over `U`.** If the structural
morphism of an algebraic space `F` over `U`, viewed over `S` by Stacks 04SG, is locally
quasi-finite, then so is the morphism from `F` to the terminal object over `U`. -/
theorem isLocallyQuasiFinite_of_algebraicSpaceMap
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (h : Space.IsLocallyQuasiFinite B S hS (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    Space.IsLocallyQuasiFinite B U.left.1 U.left.2
      ((Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from F) := by
  have h₁ : Space.IsLocallyQuasiFinite B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.locallyQuasiFiniteProperty B S hS) U F hF).mp h
  have h₂ := (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    _ F).mp h₁
  exact Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2
    (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2)
    (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2) _ _ h₂

end ReadOverU

/-- **A quasi-separated diagonal makes `Isom_𝒳(x, x)` quasi-separated.** If the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is quasi-separated in the sense of Stacks 04XB, then the automorphism space
`Isom_𝒳(x, x)`, the base change of `Δ` along `(x, x)`, is quasi-separated over `U`. -/
theorem isQuasiSeparatedOver_isomSpace_of_diagonal
    (h : IsQuasiSeparated B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val)) :
    Space.IsQuasiSeparatedOver B U.left.1 U.left.2 (isomSpace B S hS 𝒳.val U x x) :=
  isQuasiSeparatedOver_of_algebraicSpaceMap _
    (prop_isomSpace_of_diagonal B S hS 𝒳 U x (Space.quasiSeparatedProperty B S hS) h)

/-- **A locally separated diagonal makes `Isom_𝒳(x, x)` locally separated.** If the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is locally separated in the sense of Stacks 04XB, then the automorphism space
`Isom_𝒳(x, x)`, the base change of `Δ` along `(x, x)`, is locally separated over `U`. -/
theorem isLocallySeparatedOver_isomSpace_of_diagonal
    (h : IsLocallySeparated B S hS (diagonal.{u, u, u + 1} B S hS 𝒳.val)) :
    Space.IsLocallySeparatedOver B U.left.1 U.left.2 (isomSpace B S hS 𝒳.val U x x) :=
  isLocallySeparatedOver_of_algebraicSpaceMap _
    (prop_isomSpace_of_diagonal B S hS 𝒳 U x (Space.locallySeparatedMorphismProperty B S hS) h)

/-- **On a quasi-DM algebraic stack `Isom_𝒳(x, x)` is locally quasi-finite.** If `𝒳` is
quasi-DM (Stacks 050D), then it is quasi-DM over `S` (Stacks 050N), so the relative diagonal of
its structure morphism, and hence the absolute diagonal, is locally quasi-finite in the sense of
Stacks 04XB; its base change `Isom_𝒳(x, x) ⟶ U` along `(x, x)` is therefore locally
quasi-finite. -/
theorem isLocallyQuasiFinite_isomSpace_of_isAbsolutelyQuasiDM
    (h : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳) :
    Space.IsLocallyQuasiFinite B U.left.1 U.left.2
      ((Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from
        (isomSpace B S hS 𝒳.val U x x)) :=
  isLocallyQuasiFinite_of_algebraicSpaceMap _
    (prop_isomSpace_of_diagonal B S hS 𝒳 U x (Space.locallyQuasiFiniteProperty B S hS)
      ((relativeProperty_diagonal_iff_relativeDiagonal_structureMorphism.{u, w} B S hS 𝒳
        (Space.locallyQuasiFiniteProperty B S hS)).mpr
        ((AlgebraicStacks.isAbsolutelyQuasiDM_iff_isQuasiDMOver.{u, w} B S hS B.contains_terminal
          𝒳).mp h)))

/-- **A quasi-separated inertia projection makes `Isom_𝒳(x, x)` quasi-separated.** If
`π : I_𝒳 ⟶ 𝒳` is quasi-separated in the sense of Stacks 04XB, then `Isom_𝒳(x, x)`, the base
change of `π` along `x`, is quasi-separated over `U`. -/
theorem isQuasiSeparatedOver_isomSpace_of_inertiaProjection
    (h : IsQuasiSeparated B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom) :
    Space.IsQuasiSeparatedOver B U.left.1 U.left.2 (isomSpace B S hS 𝒳.val U x x) :=
  isQuasiSeparatedOver_of_algebraicSpaceMap _
    (prop_isomSpace_of_inertiaProjection B S hS 𝒳 U x (Space.quasiSeparatedProperty B S hS) h)

/-- **A locally separated inertia projection makes `Isom_𝒳(x, x)` locally separated.** If
`π : I_𝒳 ⟶ 𝒳` is locally separated in the sense of Stacks 04XB, then `Isom_𝒳(x, x)`, the base
change of `π` along `x`, is locally separated over `U`. -/
theorem isLocallySeparatedOver_isomSpace_of_inertiaProjection
    (h : IsLocallySeparated B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom) :
    Space.IsLocallySeparatedOver B U.left.1 U.left.2 (isomSpace B S hS 𝒳.val U x x) :=
  isLocallySeparatedOver_of_algebraicSpaceMap _
    (prop_isomSpace_of_inertiaProjection B S hS 𝒳 U x
      (Space.locallySeparatedMorphismProperty B S hS) h)

/-- **A locally quasi-finite inertia projection makes `Isom_𝒳(x, x)` locally quasi-finite.** If
`π : I_𝒳 ⟶ 𝒳` is locally quasi-finite in the sense of Stacks 04XB, then so is its base change
`Isom_𝒳(x, x) ⟶ U` along `x`. -/
theorem isLocallyQuasiFinite_isomSpace_of_inertiaProjection
    (h : IsLocallyQuasiFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom) :
    Space.IsLocallyQuasiFinite B U.left.1 U.left.2
      ((Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from
        (isomSpace B S hS 𝒳.val U x x)) :=
  isLocallyQuasiFinite_of_algebraicSpaceMap _
    (prop_isomSpace_of_inertiaProjection B S hS 𝒳 U x (Space.locallyQuasiFiniteProperty B S hS) h)

end AlgebraicGeometry.Stack
