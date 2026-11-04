module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal

/-!
# Algebraic stacks with quasi-affine diagonal

A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is quasi-affine* in the sense of Stacks 04XB when every
algebraic space representing its base change along a scheme-valued point of the target has
quasi-affine structural morphism (Stacks 03WL), read as a morphism of algebraic spaces over `S`.
An algebraic stack has *quasi-affine diagonal* when its diagonal `𝒳 ⟶ 𝒳 × 𝒳`, which is always
representable by algebraic spaces, is quasi-affine in this sense.

## Main definitions

* `AlgebraicGeometry.Stack.IsQuasiAffineHom`: the Stacks 04XB notion at
  `AlgebraicGeometry.Space.IsQuasiAffineHom`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiAffineHom_isomSpace`: for an algebraic stack with quasi-affine
  diagonal, the structural morphism of every isomorphism space `Isom(x, y)`, read over `S`, is
  quasi-affine.
* `AlgebraicGeometry.Stack.exists_isomSpace_representing`: that morphism is represented by a
  quasi-affine morphism of the site.

## Implementation notes

The predicate is written out, as `AlgebraicGeometry.Stack.IsAffineHom` is, rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty`: the latter carries instance hypotheses on the tested
property which are not available for quasi-affine morphisms of algebraic spaces, while its body
uses neither.

## References

* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u v w

section FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` *is
quasi-affine* when every algebraic space representing its base change along a scheme-valued point
of the target has quasi-affine structural morphism (Stacks 03WL), read as a morphism of algebraic
spaces over `S`. This is the notion of Stacks 04XB for `AlgebraicGeometry.Space.IsQuasiAffineHom`.
-/
abbrev IsQuasiAffineHom (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsQuasiAffineHom B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The isomorphism spaces of an algebraic stack with quasi-affine diagonal are quasi-affine.**
For objects `x`, `y` of the fibre over `U`, the structural morphism of `Isom(x, y)`, read as a
morphism of algebraic spaces over `S`, is quasi-affine in the sense of Stacks 03WL. -/
theorem isQuasiAffineHom_isomSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳)) (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) :
    Space.IsQuasiAffineHom B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
          ⟨isomSpace B S hS 𝒳 U x y, isAlgebraicSpace_isomSpace B S hS 𝒳 h𝒳 U x y⟩)).hom := by
  have hp := 𝒳.isFiberedInGroupoids
  have hpf : 𝒳.val.p.IsFibered := hp.isFibered
  have h₁ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p U x
  have h₂ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p U y
  have hY : pairFunctor h₁ h₂ ⋙ ProdP 𝒳.val.p = Over.map U.hom := pairFunctor_comp h₁ h₂
  refine hΔ U (pairFunctor h₁ h₂) hY _ _ ?_
  exact (nonempty_equivalenceOver_fst_iff hp hY _).2
    ⟨Functor.isoWhiskerRight (Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.p U x y hp)
      uliftFunctor.{u, u}⟩

/-- The underlying presheaf of `Isom(x, y)` read as an algebraic space over `S` is the presheaf
of pairs `(φ, m)` of a morphism `φ : V ⟶ U` and an isomorphism `m : φ^* x ≅ φ^* y`. -/
theorem isomSpace_spacesOverSmallerBase_left
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (U : BigFppfOver B S hS)
    (x y : 𝒳.val.p.Fiber U) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
      ⟨isomSpace B S hS 𝒳 U x y, isAlgebraicSpace_isomSpace B S hS 𝒳 h𝒳 U x y⟩).1.left =
      OverShriek.presheaf ((Over.iteratedSliceForward (Over.mk U.hom)).op ⋙
        isomSpace B S hS 𝒳 U x y) :=
  rfl

section Pairs

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (T : BigFppfOver B S hS)
  {Z₁ Z₂ : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.obj}
  (h₁ : Z₁ ⋙ 𝒳.val.p = Over.map T.hom) (h₂ : Z₂ ⋙ 𝒳.val.p = Over.map T.hom)

/-- The presheaf on the big fppf site of `T` of vertical morphisms between the values of two
scheme-valued points `Z₁`, `Z₂` of `𝒳` over `T`: the isomorphism presheaf of the pair. -/
noncomputable abbrev pairIsomPresheaf : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u :=
  VertHom.presheaf 𝒳.isFiberedInGroupoids h₁ h₂

/-- The isomorphism presheaf of a pair of scheme-valued points of an algebraic stack is an
algebraic space over the base of the points: the diagonal is representable by algebraic spaces,
and the fibre of the diagonal at the pair is the category of elements of that presheaf. -/
theorem isAlgebraicSpace_pairIsomPresheaf (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsAlgebraicSpace B T.left.1 T.left.2 (pairIsomPresheaf B S hS 𝒳 T h₁ h₂) := by
  have hp := 𝒳.isFiberedInGroupoids
  obtain ⟨hg, -, hdiag, -⟩ := h𝒳
  have he : CatFiberedInGroupoids.mk 𝒳.val hg = 𝒳 := Subtype.ext rfl
  rw [he] at hdiag
  have hY : pairFunctor h₁ h₂ ⋙ ProdP 𝒳.val.p = Over.map T.hom := pairFunctor_comp h₁ h₂
  obtain ⟨F, hF, hE⟩ := hdiag T (pairFunctor h₁ h₂) hY
  obtain ⟨i⟩ := (nonempty_equivalenceOver_fst_iff hp hY F).1 hE
  exact isAlgebraicSpace_of_iso B T.left.1 T.left.2
    (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso i) hF

/-- The isomorphism presheaf of a pair of scheme-valued points, read as an algebraic space over
`S` with its structural morphism to `T`. -/
noncomputable abbrev pairIsomSpace (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    SpacesOverSmallerBase B T.left.1 S T.left.2 hS T.hom :=
  (spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj
    ⟨pairIsomPresheaf B S hS 𝒳 T h₁ h₂, isAlgebraicSpace_pairIsomPresheaf B S hS 𝒳 T h₁ h₂ h𝒳⟩

/-- **For an algebraic stack with quasi-affine diagonal the isomorphism space of a pair of
scheme-valued points is quasi-affine over their base.** -/
theorem isQuasiAffineHom_pairIsomSpace (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳)) :
    Space.IsQuasiAffineHom B S hS (pairIsomSpace B S hS 𝒳 T h₁ h₂ h𝒳).1.hom := by
  have hp := 𝒳.isFiberedInGroupoids
  have hY : pairFunctor h₁ h₂ ⋙ ProdP 𝒳.val.p = Over.map T.hom := pairFunctor_comp h₁ h₂
  refine hΔ T (pairFunctor h₁ h₂) hY _ _ ?_
  exact (nonempty_equivalenceOver_fst_iff hp hY _).2 ⟨Iso.refl _⟩

/-- **The isomorphism space of a pair of scheme-valued points of an algebraic stack with
quasi-affine diagonal is represented by a quasi-affine morphism of the site.** -/
theorem exists_pairIsomSpace_representing (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳)) :
    ∃ (Q : BigFppfOver B S hS) (π : Q ⟶ T)
      (e : yoneda.obj Q ≅ (pairIsomSpace B S hS 𝒳 T h₁ h₂ h𝒳).1.left),
      e.hom ≫ (pairIsomSpace B S hS 𝒳 T h₁ h₂ h𝒳).1.hom = yoneda.map π ∧
        _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map π) := by
  have hq := Space.presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS
    (pairIsomSpace B S hS 𝒳 T h₁ h₂ h𝒳).property (isAlgebraicSpace_yoneda B S hS (Over.mk T.hom))
    (isQuasiAffineHom_pairIsomSpace B S hS 𝒳 T h₁ h₂ h𝒳 hΔ)
  obtain ⟨Q, π, fst, hpb⟩ := hq.rep (𝟙 _)
  have : IsIso fst := hpb.isIso_fst_of_isIso
  exact ⟨Q, π, asIso fst, by simpa using hpb.w, hq.property _ _ _ hpb⟩

end Pairs

end AlgebraicGeometry.Stack

end
