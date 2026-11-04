module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Fibre products over a presheaf covered by open algebraic subspaces

Let `F` be a presheaf on the big fppf site of `S` and let `p : P ⟶ F` be a relative open
immersion whose source is an algebraic space. For any two objects `a` and `b` of the site
and any `u : yoneda.obj a ⟶ F`, `v : yoneda.obj b ⟶ F`, the pullback of `p` along the
canonical map `yoneda.obj a ×_F yoneda.obj b ⟶ F` is again representable, and the resulting
morphism into `yoneda.obj a ×_F yoneda.obj b` is a relative open immersion.

The representing object is `(a ×_F P) ×_P (b ×_F P)`, where `a ×_F P` and `b ×_F P` are the
open subschemes of `a` and of `b` cut out by `P`.

## Main results

* `AlgebraicGeometry.Space.inverseImage_isOpenImmersion_le_monomorphisms`: a morphism of the
  big fppf category over `S` whose underlying morphism of schemes is an open immersion is a
  monomorphism.
* `AlgebraicGeometry.Space.mono_of_presheaf_isOpenImmersion`: a relative open immersion of
  presheaves is a monomorphism.
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_forall`: a presheaf has a
  representable diagonal as soon as every morphism to it from a representable presheaf is
  relatively representable.
* `AlgebraicGeometry.Space.exists_isPullback_of_presheaf_isOpenImmersion`: the fibre product
  of `yoneda.obj a ×_F yoneda.obj b` with `P` over `F` is representable, by an object
  obtained as `(a ×_F P) ×_P (b ×_F P)`, and the projection to `yoneda.obj a ×_F yoneda.obj b`
  is a relative open immersion.

## Implementation notes

Binary products in the big fppf category over `S` are Mathlib's binary products in a slice,
constructed from fibre products and installed as a local instance.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the big fppf category over `S` whose underlying morphism of schemes is an
open immersion is a monomorphism. -/
lemma inverseImage_isOpenImmersion_le_monomorphisms :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty
      Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
  intro _ _ f hf
  have : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map f) := hf
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance

/-- A relative open immersion of presheaves on the big fppf site of `S` is a monomorphism. -/
lemma mono_of_presheaf_isOpenImmersion {F P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : P ⟶ F}
    (hp : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) : Mono p :=
  MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone inverseImage_isOpenImmersion_le_monomorphisms _ hp)

/-- A presheaf on the big fppf site of `S` has a representable diagonal as soon as every
morphism to it from a representable presheaf is relatively representable. -/
lemma relativelyRepresentable_diag_of_forall {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : ∀ ⦃a : BigFppfOver B S hS⦄ (q : yoneda.obj a ⟶ F),
      yoneda.relativelyRepresentable q) :
    yoneda.relativelyRepresentable (diag F) :=
  Functor.relativelyRepresentable.diag_of_map_from_obj h

/-- Let `p : P ⟶ F` be a relative open immersion of presheaves on the big fppf site of `S`
whose source has a representable diagonal — for instance an open algebraic subspace of `F`.
Then for any two morphisms `u : yoneda.obj a ⟶ F` and `v : yoneda.obj b ⟶ F` from
representable presheaves, the fibre product of `P` and `yoneda.obj a ×_F yoneda.obj b` over
`F` is representable, and its projection to `yoneda.obj a ×_F yoneda.obj b` is again a
relative open immersion. -/
lemma exists_isPullback_of_presheaf_isOpenImmersion
    {F P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : P ⟶ F}
    (hp : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hP : yoneda.relativelyRepresentable (diag P))
    {a b : BigFppfOver B S hS} (u : yoneda.obj a ⟶ F) (v : yoneda.obj b ⟶ F) :
    ∃ (W : BigFppfOver B S hS) (w : yoneda.obj W ⟶ pullback u v) (m : yoneda.obj W ⟶ P),
      IsPullback w m (pullback.fst u v ≫ u) p ∧
        (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
          MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf w := by
  have hrep := hp.rep
  have hV := hrep.isPullback u
  have hV' := hrep.isPullback v
  have hα : yoneda.relativelyRepresentable (hrep.fst u) :=
    Functor.relativelyRepresentable.of_diag hP (hrep.fst u)
  have hW := hα.isPullback (hrep.fst v)
  have h1 : hα.fst (hrep.fst v) ≫ hrep.fst u
      = yoneda.map (hα.snd (hrep.fst v)) ≫ hrep.fst v := hW.w
  have hcomm : (hα.fst (hrep.fst v) ≫ yoneda.map (hrep.snd u)) ≫ u
      = (yoneda.map (hα.snd (hrep.fst v)) ≫ yoneda.map (hrep.snd v)) ≫ v := by
    simp only [Category.assoc, ← hV.w, ← hV'.w]
    rw [← Category.assoc, h1, Category.assoc]
  set w := pullback.lift _ _ hcomm
  have hwfst : w ≫ pullback.fst u v
      = hα.fst (hrep.fst v) ≫ yoneda.map (hrep.snd u) := pullback.lift_fst _ _ _
  have hwsnd : w ≫ pullback.snd u v
      = yoneda.map (hα.snd (hrep.fst v)) ≫ yoneda.map (hrep.snd v) := pullback.lift_snd _ _ _
  have hsq : w ≫ (pullback.fst u v ≫ u)
      = (hα.fst (hrep.fst v) ≫ hrep.fst u) ≫ p := by
    rw [← Category.assoc, hwfst, Category.assoc, ← hV.w, ← Category.assoc]
  have key : IsPullback w (hα.fst (hrep.fst v) ≫ hrep.fst u) (pullback.fst u v ≫ u) p := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq
      (fun s => hW.lift
        (hV.lift s.snd (s.fst ≫ pullback.fst u v) (by
          rw [Category.assoc]; exact s.condition.symm))
        (hV'.lift s.snd (s.fst ≫ pullback.snd u v) (by
          rw [Category.assoc, ← pullback.condition]; exact s.condition.symm))
        (by rw [IsPullback.lift_fst, IsPullback.lift_fst])) ?_ ?_ ?_)
    · intro s
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hwfst, ← Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd]
      · rw [Category.assoc, hwsnd, ← Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd]
    · intro s
      rw [← Category.assoc, IsPullback.lift_fst, IsPullback.lift_fst]
    · intro s y hy₁ hy₂
      refine hW.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst]
        refine hV.hom_ext ?_ ?_
        · rw [Category.assoc, hy₂, IsPullback.lift_fst]
        · rw [Category.assoc, ← hwfst, ← Category.assoc, hy₁, IsPullback.lift_snd]
      · rw [IsPullback.lift_snd]
        refine hV'.hom_ext ?_ ?_
        · rw [IsPullback.lift_fst, Category.assoc, ← h1]
          simpa using hy₂
        · rw [Category.assoc, ← hwsnd, ← Category.assoc, hy₁, IsPullback.lift_snd]
  exact ⟨hα.pullback (hrep.fst v), w, hα.fst (hrep.fst v) ≫ hrep.fst u, key,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback key.flip hp⟩

end AlgebraicGeometry.Space

end
