module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# A formal algebraic space of finite type over a locally Noetherian one: the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that belong with
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian`. A declaration of that module
whose statement the round strengthened keeps its original statement there; its strengthened form
lives here under a primed name.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AQ7.** If `Y` is a locally Noetherian formal algebraic space
over `S` and `f : X ⟶ Y` is a morphism of formal algebraic spaces over `S` which is locally of
finite type, then `X` is locally Noetherian.

The atlas of `Y` by Noetherian affine formal algebraic spaces base changes to a family of
fibre products covering `X`, and the atlases of those fibre products assemble into an atlas of
`X`. Its members are locally of finite type over the members of the atlas of `Y` by Stacks
0ANL, condition (1) implies condition (3), hence Noetherian by clause (5) of Stacks 0AKQ,
which Stacks 0AKN makes unconditional.

The fibre products `Vⱼ ×_Y X` are formal algebraic spaces by **Stacks 0AJ3**, which this
library proves outright for a base which is a formal algebraic space. -/
@[stacks 0AQ7]
theorem isLocallyNoetherian_source_of_isLocallyOfFiniteType'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsLocallyNoetherian B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyNoetherian B S hS X := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hYformal, J, V, v, hVaffine, hVetale, hVsurj, hVnoeth⟩ := hY
  have hWformal : ∀ j, IsFormalAlgebraicSpace B S hS (pullback (v j) f) := fun j ↦
    isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS (v j) f hYformal
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hVaffine j)) hX
  have hWatlas : ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS)
      (w : ∀ i, U i ⟶ pullback (v j) f),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (U i)) ∧
      (∀ i, IsRepresentableEtale B S hS (w i)) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) := fun j ↦ (hWformal j).2
  choose I U w hUaffine hUetale hUsurj using hWatlas
  have hUetaleX : ∀ p : Σ j, I j,
      IsRepresentableEtale B S hS (w p.1 p.2 ≫ pullback.snd (v p.1) f) := fun p ↦
    IsRepresentableEtale.comp B S hS (hUetale p.1 p.2)
      (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVetale p.1))
  refine ⟨hX, (Σ j, I j), fun p ↦ U p.1 p.2,
    fun p ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f, fun p ↦ hUaffine p.1 p.2, hUetaleX, ?_,
    fun p ↦ ?_⟩
  · let e : (∐ fun p : Σ j, I j ↦ U p.1 p.2) ⟶ (∐ fun j ↦ pullback (v j) f) :=
      Sigma.desc fun p ↦ w p.1 p.2 ≫ Sigma.ι (fun j ↦ pullback (v j) f) p.1
    have : ∀ j, Epi (Sigma.desc (w j)) := fun j ↦
      (Sheaf.isLocallySurjective_iff_epi _).mp (hUsurj j)
    have he : Epi e := ⟨fun k l hkl ↦ Sigma.hom_ext _ _ fun j ↦
      (cancel_epi (Sigma.desc (w j))).1 <| Sigma.hom_ext _ _ fun i ↦ by
        simpa [e] using congrArg (Sigma.ι (fun p : Σ j, I j ↦ U p.1 p.2) ⟨j, i⟩ ≫ ·) hkl⟩
    have hcomp : e ≫ (Sigma.desc fun j ↦ pullback.snd (v j) f) =
        Sigma.desc fun p : Σ j, I j ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f :=
      Sigma.hom_ext _ _ fun p ↦ by simp [e]
    have _ : Epi (Sigma.desc fun j ↦ pullback.snd (v j) f) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVsurj)
    rw [← hcomp]
    exact (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance
  · have hft : IsLocallyOfFiniteType B S hS (w p.1 p.2 ≫ pullback.fst (v p.1) f) :=
      isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType B S hS f hf
        (U p.1 p.2) (V p.1) (w p.1 p.2 ≫ pullback.snd (v p.1) f) (v p.1)
        (w p.1 p.2 ≫ pullback.fst (v p.1) f)
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hUaffine p.1 p.2))
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hVaffine p.1))
        (hUetaleX p) (hVetale p.1)
        (by rw [Category.assoc, Category.assoc, ← pullback.condition])
    exact isNoetherian_of_isRepresentable' B S hS (w p.1 p.2 ≫ pullback.fst (v p.1) f)
      (hUaffine p.1 p.2) (hVnoeth p.1).1.1 hft.1 hft (hVnoeth p.1)

/-- **Stacks 0AQ8.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of formal
algebraic spaces over `S`. If `Z` is locally Noetherian and `f` is locally of finite type, then
`Z ×_Y X` is locally Noetherian.

The projection `p : Z ×_Y X ⟶ Z` is a base change of `f`, so it is locally of finite type by
Stacks 0AQ5, and `Z ×_Y X` is a formal algebraic space by Stacks 0AJ3; Stacks 0AQ7 applies to
`p`. The fibre product is presented as an arbitrary cartesian square, so the statement covers
either order of its two legs. -/
@[stacks 0AQ8 "stated for an arbitrary cartesian square over `Y` rather than for the chosen \
fibre product `Z ×_Y X`"]
theorem isLocallyNoetherian_of_isPullback'
    {W X Y Z : FppfSheaf B S hS} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyNoetherian B S hS W :=
  isLocallyNoetherian_source_of_isLocallyOfFiniteType' B S hS p
    (isFormalAlgebraicSpace_of_iso B S hS sq.isoPullback
      (isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS g f hY hZ.1 hX))
    hZ (IsLocallyOfFiniteType.of_isPullback B S hS sq hf)

end AlgebraicGeometry.FormalSpace

end
