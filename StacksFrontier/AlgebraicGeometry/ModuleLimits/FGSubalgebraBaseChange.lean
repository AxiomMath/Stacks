module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.Algebra.Module.Adequate.FiniteTypeSubalgebras

/-!
# Invertible modules on a base change descend to a finitely generated subalgebra

Let `X` be a quasi-compact quasi-separated scheme over a commutative ring `k` and let `A` be a
`k`-algebra. Writing `A` as the filtered colimit of its finitely generated `k`-subalgebras, the
base change `X_A = Spec A ×_{Spec k} X` is the cofiltered limit of the base changes `X_{A'}`, with
affine transition morphisms; so by [Stacks, Tag 0B8W] (2) every invertible module on `X_A` is the
pullback of an invertible module on some `X_{A'}`.

## Implementation notes

The presentation of `X_A` as the cofiltered limit of the `X_{A'}`, with affine transition
morphisms, is built inside the proof and fed to Tag 0B8W (2),
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit`. Its starting
point is `Stacks.Adequate.isColimit_fgSubalgebraCocone`, the filtered colimit expressing `A` as
the union of its finitely generated `k`-subalgebras; `Spec` on algebras turns that into the limit
of the `Spec A'` over `Spec k`, and base change along `f` into the limit of the `X_{A'}`.

## Main results

* `Stacks.FGSubalgebraLimit.exists_fg_subalgebra_isInvertible_pullback_iso`.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.FGSubalgebraLimit

/-- **Invertible modules on a base change descend to a finitely generated subalgebra.** Let `X`
be a quasi-compact quasi-separated scheme over a commutative ring `k` and let `A` be a
`k`-algebra. Every invertible module on `X_A` is the pullback of an invertible module on `X_{A'}`
for some finitely generated `k`-subalgebra `A' ⊆ A`, along the morphism `X_A ⟶ X_{A'}` covering
`Spec A ⟶ Spec A'` and commuting with the projections to `X`. -/
theorem exists_fg_subalgebra_isInvertible_pullback_iso
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).Modules)
    (hL : SheafOfModules.IsInvertible
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).sheaf.obj
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f).ringCatSheaf.property L) :
    ∃ (A' : Subalgebra k A) (_ : A'.FG)
      (L' : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f).Modules),
      SheafOfModules.IsInvertible
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f).sheaf.obj
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f).ringCatSheaf.property L' ∧
        ∃ p : pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ⟶
              pullback (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f,
          p ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f =
              pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ≫
                Spec.map (CommRingCat.ofHom (Subalgebra.val A').toRingHom) ∧
            p ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A'))) f =
              pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f ∧
            Nonempty (L ≅ (Scheme.Modules.pullback p).obj L') := by
  classical
  -- `A` is the filtered colimit of its finitely generated `k`-subalgebras
  let J := Stacks.Adequate.FgSubalgebras k A
  let F : J ⥤ CommAlgCat.{u} k := Stacks.Adequate.fgSubalgebraDiagram k A
  let cc : Cocone F := Stacks.Adequate.fgSubalgebraCocone k A
  let hcc : IsColimit cc := Stacks.Adequate.isColimit_fgSubalgebraCocone k A
  -- hence `X_A` is the cofiltered limit of the base changes `X_{A'}`, with affine transitions
  let G : Jᵒᵖ ⥤ Over (Spec (.of k)) := F.op ⋙ algSpec (CommRingCat.of k)
  let D : Jᵒᵖ ⥤ Scheme.{u} := G ⋙ Over.pullback f ⋙ Over.forget X
  have : PreservesLimitsOfSize.{u, u} (algSpec (CommRingCat.of k)) :=
    preservesLimitsOfSize_algSpec
  let hG : IsLimit ((algSpec (CommRingCat.of k)).mapCone cc.op) := isLimitOfPreserves _ hcc.op
  let c : Cone D := (Over.forget X).mapCone ((Over.pullback f).mapCone
    ((algSpec (CommRingCat.of k)).mapCone cc.op))
  have hc : IsLimit c := isLimitOfPreserves _ (isLimitOfPreserves _ hG)
  have : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := fun g => by
    refine MorphismProperty.overPullbackMap (P := @IsAffineHom) f (G.map g) ?_
    show IsAffineHom (Spec.map _)
    infer_instance
  have haff (i : Jᵒᵖ) : IsAffineHom (pullback.snd (G.obj i).hom f) := by
    have : IsAffine (G.obj i).left := by
      show IsAffine (Spec _); infer_instance
    have : IsAffineHom (G.obj i).hom := isAffineHom_of_isAffine _
    first
      | exact isAffineHom_isStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback (G.obj i).hom f).flip this
      | exact isAffineHom_isStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback (G.obj i).hom f) this
  have (i : Jᵒᵖ) : CompactSpace (D.obj i) :=
    have := haff i
    ⟨QuasiCompact.isCompact_preimage (f := pullback.snd (G.obj i).hom f)
      _ isOpen_univ isCompact_univ⟩
  have (i : Jᵒᵖ) : QuasiSeparatedSpace (D.obj i) :=
    have := haff i
    have hsep : IsSeparated (pullback.snd (G.obj i).hom f) := IsSeparated.of_isAffineHom _
    have hq : QuasiSeparated (pullback.snd (G.obj i).hom f) := inferInstance
    @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd (G.obj i).hom f) inferInstance hq
  obtain ⟨i, L', hL', ⟨e⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit D c hc L hL
  refine ⟨(i.unop : Subalgebra k A), i.unop.2, L', hL', c.π.app i, ?_, ?_, ⟨e⟩⟩
  all_goals show pullback.lift (pullback.fst _ f ≫ _) (pullback.snd _ f) _ ≫ _ = _
  exacts [(pullback.lift_fst _ _ _).trans rfl, (pullback.lift_snd _ _ _).trans rfl]

end Stacks.FGSubalgebraLimit

end
