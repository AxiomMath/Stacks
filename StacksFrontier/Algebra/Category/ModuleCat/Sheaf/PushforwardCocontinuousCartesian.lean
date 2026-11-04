module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianPushoutTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous

/-!
# The direct image along a cocontinuous functor is cartesian over terminal arrows

Let `w : X ⥤ Y` be a functor, `S`, `T` presheaves of commutative rings on `X` and `Y`, and
`ψ : T ⟶ w_* S` a structure map, so that the right Kan extension `w_* M` of a presheaf of
`S`-modules `M` is a presheaf of `T`-modules (`Stacks.SheafOfModules.ranObj`). Let `φ : y ⟶ y'` be
an arrow of `Y` such that both comma categories `CostructuredArrow w y` and
`CostructuredArrow w y'` have terminal objects `t = (x₀, w x₀ ⟶ y)` and `t' = (x₀', w x₀' ⟶ y')`,
and let `k : x₀ ⟶ x₀'` be the arrow induced by terminality of `t'`. Then the sections of `w_* M`
over `y` and `y'` are those of `M` over `x₀` and `x₀'`, and the restriction map of `w_* M` along
`φ` is that of `M` along `k`. So if the square of rings
```
  T(y') ⟶ S(x₀')
    |        |
  T(y)  ⟶ S(x₀)
```
is a pushout and `M` is cartesian over `k`, then `w_* M` is cartesian over `φ`
(`Stacks.SheafOfModules.bijective_restrictionBaseChange_ranObj_of_isTerminal`).

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks representable by affine schemes this is the
algebraic half of the proof that `f_*` preserves the flat base change property (Stacks 0765,
clause (4) of Stacks 076Z): the square of rings is the square of global functions of the fibre
product square `x₀ = y ×_𝒴 𝒳`.

## Main results

* `Stacks.SheafOfModules.isIso_ranπ_of_isTerminal`: the leg of the right Kan extension at a
  terminal arrow is an isomorphism.
* `Stacks.SheafOfModules.bijective_restrictionBaseChange_ranObj_of_isTerminal`: the direct image
  is cartesian over an arrow between objects with terminal arrows.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v₂ u₂ r m

namespace Stacks.SheafOfModules

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)

/-- The leg of the right Kan extension along `w.op` at a terminal arrow `(x₀, w x₀ ⟶ y)` of
`CostructuredArrow w y` is an isomorphism: that arrow is initial among the legs. -/
theorem isIso_ranπ_of_isTerminal {H : Type*} [Category H] (N : Xᵒᵖ ⥤ H)
    [∀ F : Xᵒᵖ ⥤ H, w.op.HasRightKanExtension F] [w.op.HasPointwiseRightKanExtension N]
    {y : Y} {t : CostructuredArrow w y} (ht : IsTerminal t) :
    IsIso (ranπ w.op N (op y) (StructuredArrow.mk (Y := op t.left) t.hom.op)) :=
  (ranIsLimit w.op N (op y)).isIso_π_app_of_isInitial _
    ((initialOpOfTerminal ht).isInitialObj (costructuredArrowOpEquivalence w y).functor)

variable {S : Xᵒᵖ ⥤ CommRingCat.{r}} {T : Yᵒᵖ ⥤ CommRingCat.{r}}
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{max m r}, w.op.HasPointwiseRightKanExtension F]
  (ψ : T ⋙ forget₂ CommRingCat RingCat ⟶ w.op.ran.obj (S ⋙ forget₂ CommRingCat RingCat))

/-- **The direct image is cartesian over an arrow between objects with terminal arrows**, as soon
as the module is cartesian over the induced arrow `k : x₀ ⟶ x₀'` and the square of rings
`T(y') → T(y)`, `S(x₀') → S(x₀)` through the structure map is a pushout. The ring maps
`a : T(y) ⟶ S(x₀)` and `a' : T(y') ⟶ S(x₀')` are the ones the structure map cuts out at the
terminal arrows (`Stacks.SheafOfModules.scalarπ`), given in `CommRingCat`. -/
theorem bijective_restrictionBaseChange_ranObj_of_isTerminal
    (M : PresheafOfModules.{max m r} (S ⋙ forget₂ CommRingCat RingCat.{r}))
    {y y' : Y} (φ : y ⟶ y') {t : CostructuredArrow w y} (ht : IsTerminal t)
    {t' : CostructuredArrow w y'} (ht' : IsTerminal t')
    (a : T.obj (op y) ⟶ S.obj (op t.left)) (a' : T.obj (op y') ⟶ S.obj (op t'.left))
    (ha : ∀ s, (scalarπ w ψ (op y) (StructuredArrow.mk (Y := op t.left) t.hom.op)).hom s =
      a.hom s)
    (ha' : ∀ s, (scalarπ w ψ (op y') (StructuredArrow.mk (Y := op t'.left) t'.hom.op)).hom s =
      a'.hom s)
    (hpo : IsPushout a' (T.map φ.op)
      (S.map (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left.op) a)
    (hM : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange (R := S) M
      (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left.op)) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange (R := T)
      (ranObj w ψ M) φ.op) := by
  let k : t.left ⟶ t'.left := (ht'.from (CostructuredArrow.mk (t.hom ≫ φ))).left
  have hk : w.map k ≫ t'.hom = t.hom ≫ φ := CostructuredArrow.w (ht'.from _)
  let j : StructuredArrow (op y) w.op := StructuredArrow.mk (Y := op t.left) t.hom.op
  let j' : StructuredArrow (op y') w.op := StructuredArrow.mk (Y := op t'.left) t'.hom.op
  have := isIso_ranπ_of_isTerminal w M.presheaf ht
  have := isIso_ranπ_of_isTerminal w M.presheaf ht'
  let eY := (asIso (ranπ w.op M.presheaf (op y) j)).addCommGroupIsoToAddEquiv
  let eX := (asIso (ranπ w.op M.presheaf (op y') j')).addCommGroupIsoToAddEquiv
  have hsmul : ∀ (z : Yᵒᵖ) (i : StructuredArrow z w.op) (s : T.obj z)
      (x : (ranObj w ψ M).obj z),
      (ranπ w.op M.presheaf z i).hom (s • x) =
        (scalarπ w ψ z i).hom s • (ranπ w.op M.presheaf z i).hom x := fun z i s x =>
    ConcreteCategory.congr_hom (ranSMul_π w ψ M z s i) x
  refine Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_isPushout
    (ranObj w ψ M) M φ.op k.op a' a hpo eX eY (fun s x => ?_) (fun s x => ?_) (fun x => ?_) hM
  · exact (hsmul _ j' s x).trans (by rw [ha']; rfl)
  · exact (hsmul _ j s x).trans (by rw [ha]; rfl)
  · let g : j' ⟶ (StructuredArrow.map φ.op).obj j :=
      StructuredArrow.homMk k.op (by
        change t'.hom.op ≫ (w.map k).op = φ.op ≫ t.hom.op
        rw [← op_comp, hk, op_comp])
    exact (ConcreteCategory.congr_hom (ranπ_map w.op M.presheaf φ.op j) x).trans
      (ConcreteCategory.congr_hom (ranπ_naturality w.op M.presheaf g) x).symm

end Stacks.SheafOfModules
