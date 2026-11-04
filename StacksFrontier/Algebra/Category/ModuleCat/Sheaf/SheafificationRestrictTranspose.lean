module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationRestrictCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekObjectNaturality

/-!
# Transposing the commutation of sheafification with restriction along a cocontinuous functor

`Stacks.SheafOfModules.sheafificationCompRestrictIso` compares the two left adjoints of one
functor, so it has no elementwise description: a consumer that meets it has to transpose it away
rather than evaluate it. This file does that, and then reads the result on underlying presheaves
of abelian groups, where it becomes concrete.

The first step is formal. The comparison is a `CategoryTheory.Adjunction.leftAdjointUniq`, whose
defining property is exactly that transposing its inverse along the second adjunction gives the
transpose along the first; that is
`CategoryTheory.Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp` at
`Stacks.SheafOfModules.sheafificationCompRestrictIso_eq`.

The second step is where the arithmetic is. The transpose along the first adjunction — the one
whose left adjoint sheafifies and then restricts — is, by
`Stacks.CategoryTheory.comp_homEquiv_apply`, the unit of the sheafification adjunction followed by
that adjunction's right adjoint applied to the transpose along
`Stacks.SheafOfModules.RestrictRan.sheafAdjunction`. The right adjoint in question is
`SheafOfModules.forget` followed by `PresheafOfModules.restrictScalars (𝟙 O)`, which is the
shape Mathlib's `PresheafOfModules.sheafificationAdjunction` has; on underlying presheaves of
abelian groups that restriction of scalars disappears, see the implementation notes.

## Main results

* `Stacks.SheafOfModules.homEquiv_sheafificationCompRestrictIso_inv_app_comp`: transposing the
  inverse of the commutation away, formally.
* `Stacks.SheafOfModules.toPresheaf_map_homEquiv_sheafificationCompRestrictIso_inv_app_comp`: that
  transpose read on underlying presheaves of abelian groups. There it is
  `CategoryTheory.toSheafify` followed by the transpose along
  `Stacks.SheafOfModules.RestrictRan.sheafAdjunction`, with no restriction of scalars, no
  sheafification adjunction and no `CategoryTheory.Adjunction.leftAdjointUniq` left in it.

## Implementation notes

*Restriction of scalars along an identity.* The right adjoint of Mathlib's sheafification
adjunction for presheaves of modules is `SheafOfModules.forget R ⋙ restrictScalars α`, and at
`α = 𝟙 O` the restriction of scalars is only *definitionally* the identity functor: comparing
`(restrictScalars (𝟙 O)).map h` with `h` makes the kernel reduce the `Module.compHom` instance on
every module of sections, which at concrete arguments is a deterministic timeout rather than a
cost. `PresheafOfModules.restrictScalarsId` is the propositional comparison, and
`PresheafOfModules.toPresheaf_map_restrictScalars_id_map` is why none of it is needed here: on
underlying presheaves of abelian groups there is nothing to compare, because restriction of
scalars along an identity changes only the action and the underlying presheaf does not see the
action. That lemma is an equality the kernel accepts by `rfl`.

*Why both `Functor.map_comp` and the restriction-of-scalars lemma have to be applied as terms.*
Neither fires under `simp only` on the goals here, with no error and no progress reported:
two spellings of one definitionally equal object occur in the goal — the underlying presheaf of
modules of a sheaf of modules, and its restriction of scalars along the identity — and the
rewriter cannot choose between them. `CategoryTheory.Functor.map_comp` is therefore supplied as
`(toPresheaf O).map_comp`, and the restriction-of-scalars step as a `congrArg`.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY] (OY : Sheaf JY RingCat.{r})
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify JY AddCommGrpCat.{v}] [JY.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify JX AddCommGrpCat.{v}] [JX.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The commutation of sheafification with restriction along a cocontinuous functor transposes
away.** Its inverse, followed by a morphism out of the restricted sheafification, transposes along
"restrict the presheaf, then sheafify" to the transposition of that morphism along "sheafify, then
restrict the sheaf".

Both composites are left adjoints of one functor and the comparison between them is
`CategoryTheory.Adjunction.leftAdjointUniq`, whose defining property this is. -/
theorem homEquiv_sheafificationCompRestrictIso_inv_app_comp
    (M : PresheafOfModules.{v} OY.obj)
    {N : _root_.SheafOfModules.{v} (RestrictRan.ringSheaf w JX JY OY)}
    (φ : (PresheafOfModules.sheafification.{v} (𝟙 OY.obj) ⋙
        _root_.SheafOfModules.pushforward.{v} (F := w)
          (𝟙 (RestrictRan.ringSheaf w JX JY OY))).obj M ⟶ N) :
    ((RestrictRan.adjunction.{v} w OY.obj).comp
          (PresheafOfModules.sheafificationAdjunction.{v} (J := JX)
            (R₀ := (RestrictRan.ringSheaf w JX JY OY).obj)
            (R := RestrictRan.ringSheaf w JX JY OY)
            (𝟙 (RestrictRan.ringSheaf w JX JY OY).obj))).homEquiv M N
        ((sheafificationCompRestrictIso.{v} w JX JY OY).inv.app M ≫ φ) =
      ((PresheafOfModules.sheafificationAdjunction.{v} (𝟙 OY.obj)).comp
        (RestrictRan.sheafAdjunction.{v} w JX JY OY)).homEquiv M N φ :=
  Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp _ _ _
    (sheafificationCompRestrictIso_eq.{v} w JX JY OY) M φ

/-- **That transpose, on underlying presheaves of abelian groups.** It is
`CategoryTheory.toSheafify` followed by the transpose along
`Stacks.SheafOfModules.RestrictRan.sheafAdjunction`.

This is the form in which the transpose can be computed: nothing on the right-hand side is an
abstract left-adjoint comparison, and in particular the
`PresheafOfModules.restrictScalars (𝟙 O)` that the sheafification adjunction's
right adjoint carries has disappeared, because on underlying presheaves of abelian groups
restriction of scalars along an identity is not merely isomorphic to the identity but equal to it
(`PresheafOfModules.toPresheaf_map_restrictScalars_id_map`). -/
theorem toPresheaf_map_homEquiv_sheafificationCompRestrictIso_inv_app_comp
    (M : PresheafOfModules.{v} OY.obj)
    {N : _root_.SheafOfModules.{v} (RestrictRan.ringSheaf w JX JY OY)}
    (φ : (PresheafOfModules.sheafification.{v} (𝟙 OY.obj) ⋙
        _root_.SheafOfModules.pushforward.{v} (F := w)
          (𝟙 (RestrictRan.ringSheaf w JX JY OY))).obj M ⟶ N) :
    (PresheafOfModules.toPresheaf.{v} OY.obj).map
        (((RestrictRan.adjunction.{v} w OY.obj).comp
            (PresheafOfModules.sheafificationAdjunction.{v} (J := JX)
              (R₀ := (RestrictRan.ringSheaf w JX JY OY).obj)
              (R := RestrictRan.ringSheaf w JX JY OY)
              (𝟙 (RestrictRan.ringSheaf w JX JY OY).obj))).homEquiv M N
          ((sheafificationCompRestrictIso.{v} w JX JY OY).inv.app M ≫ φ)) =
      CategoryTheory.toSheafify JY M.presheaf ≫
        (PresheafOfModules.toPresheaf.{v} OY.obj).map
          ((_root_.SheafOfModules.forget.{v} OY).map
            ((RestrictRan.sheafAdjunction.{v} w JX JY OY).homEquiv
              ((PresheafOfModules.sheafification.{v} (𝟙 OY.obj)).obj M) N φ)) := by
  rw [homEquiv_sheafificationCompRestrictIso_inv_app_comp,
    Stacks.CategoryTheory.comp_homEquiv_apply]
  refine Eq.trans ((PresheafOfModules.toPresheaf.{v} OY.obj).map_comp _ _) ?_
  simp only [Functor.comp_map,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact congrArg (fun z => CategoryTheory.toSheafify JY M.presheaf ≫ z)
    (PresheafOfModules.toPresheaf_map_restrictScalars_id_map _)

end Stacks.SheafOfModules

end
