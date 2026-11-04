module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationRepresented

/-!
# The algebraic stack of a quasi-separated base scheme is quasi-separated

Let `S` be a scheme of a big fppf site. The algebraic stack represented by `S` itself is, viewed
over `Spec ℤ` (Stacks 04X6), represented by the object `S ⟶ Spec ℤ` of the site of `Spec ℤ`, and
its structure morphism is induced by the unique morphism to the final object. Its relative
diagonal is therefore the diagonal of `S ⟶ Spec ℤ`, which is quasi-compact when `S` is
quasi-separated, and quasi-separated because it is a monomorphism. So the algebraic stack of a
quasi-separated scheme is quasi-separated in the absolute sense of Stacks 050D, part (8).

## Main results

* `AlgebraicGeometry.Stack.isQuasiSeparatedAbs_schemeStack_base`: the algebraic stack of a
  quasi-separated base scheme is quasi-separated.

## References

* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The diagonal of a morphism of the site whose source is quasi-separated is quasi-compact**, as
a morphism of algebraic spaces. The forgetful functor to schemes carries it to the diagonal of the
underlying morphism of schemes, up to the comparison isomorphism of fibre products, and that
diagonal is quasi-compact because the source is a quasi-separated scheme. -/
theorem isQuasiCompact_yoneda_map_diagonal {V W : BigFppfOver B S hS} (k : V ⟶ W)
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj V)] :
    Space.IsQuasiCompact B S hS (yoneda.map (pullback.diagonal k)) := by
  refine Space.isQuasiCompact_yoneda_map_of_quasiCompact B S hS _ ?_
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst k k))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd k k))
      ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map k) :=
    (IsPullback.of_hasPullback k k).map _
  have hcomp : (BigFppfOver.toScheme B S hS).map (pullback.diagonal k) ≫ hsq.isoPullback.hom =
      pullback.diagonal ((BigFppfOver.toScheme B S hS).map k) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp,
        pullback.diagonal_fst, CategoryTheory.Functor.map_id, pullback.diagonal_fst]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp,
        pullback.diagonal_snd, CategoryTheory.Functor.map_id, pullback.diagonal_snd]
  rw [show (BigFppfOver.toScheme B S hS).map (pullback.diagonal k) =
      pullback.diagonal ((BigFppfOver.toScheme B S hS).map k) ≫ hsq.isoPullback.inv by
    rw [← hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
  infer_instance

/-- **The diagonal of a morphism of the site is quasi-separated** as a morphism of algebraic
spaces: it is a monomorphism, so its own diagonal is an isomorphism, hence quasi-compact. -/
theorem isQuasiSeparated_yoneda_map_diagonal {V W : BigFppfOver B S hS} (k : V ⟶ W) :
    Space.IsQuasiSeparated B S hS (yoneda.map (pullback.diagonal k)) :=
  fun _ _ hZ g => Space.isQuasiCompactSpace_of_iso B S hS
    (asIso (pullback.fst g (pullback.diagonal (yoneda.map (pullback.diagonal k))))).symm hZ

/-- **The algebraic stack of a quasi-separated base scheme is quasi-separated over `Spec ℤ`**: the
relative diagonal of its structure morphism over `Spec ℤ` is the Yoneda image of the diagonal of
`S ⟶ Spec ℤ`, which is quasi-compact and quasi-separated. -/
theorem isQuasiSeparatedOver_viewOverInt_schemeStack [QuasiSeparatedSpace S] :
    IsQuasiSeparatedOver B _ (contains_specULiftZ B)
      (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))) := by
  let f := structureMorphism B _ (contains_specULiftZ B)
    (viewOverInt.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))))
  let V : BigFppfOver B _ (contains_specULiftZ B) := Over.mk (toIntObject B S hS)
  let W : BigFppfOver B _ (contains_specULiftZ B) :=
    Over.mk (𝟙 (B.obj (contains_specULiftZ B)))
  have hV : QuasiSeparatedSpace ((BigFppfOver.toScheme B _ (contains_specULiftZ B)).obj V) :=
    inferInstanceAs (QuasiSeparatedSpace S)
  have hrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B _ (contains_specULiftZ B)
    (schemeStack.{u, w'} B _ (contains_specULiftZ B) W).property
    ⟨yoneda.obj V, isAlgebraicSpace_yoneda B _ (contains_specULiftZ B) V,
      ⟨viewOverIntSchemeStackEquivalenceOver.{u, w, w'} B S hS⟩⟩ f.hom
  have hk : representingMap B _ (contains_specULiftZ B) _ _ (yoneda.obj V) (yoneda.obj W)
      (viewOverIntSchemeStackEquivalenceOver.{u, w, w'} B S hS)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) f.hom =
      yoneda.map (Over.mkIdTerminal.from V) :=
    (Over.mkIdTerminal.isTerminalObj yoneda _).hom_ext _ _
  exact ⟨hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal B _ (contains_specULiftZ B)
      (Space.quasiCompactProperty B _ (contains_specULiftZ B)) f.hom hrep V W
      (viewOverIntSchemeStackEquivalenceOver.{u, w, w'} B S hS)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) _ hk
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B _ _ f)
      (isQuasiCompact_yoneda_map_diagonal B _ (contains_specULiftZ B) _),
    hasRelativeProperty_relativeDiagonal_of_prop_yoneda_diagonal B _ (contains_specULiftZ B)
      (Space.quasiSeparatedProperty B _ (contains_specULiftZ B)) f.hom hrep V W
      (viewOverIntSchemeStackEquivalenceOver.{u, w, w'} B S hS)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) _ hk
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B _ _ f)
      (isQuasiSeparated_yoneda_map_diagonal B _ (contains_specULiftZ B) _)⟩

/-- **The algebraic stack of a quasi-separated base scheme is quasi-separated** in the absolute
sense of Stacks 050D, part (8). -/
theorem isQuasiSeparatedAbs_schemeStack_base [QuasiSeparatedSpace S] :
    IsQuasiSeparatedAbs.{u, w, w'} B S hS (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) :=
  isQuasiSeparatedOver_viewOverInt_schemeStack.{u, w, w'} B S hS

end AlgebraicGeometry.Stack

end
