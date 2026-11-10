module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# The action over an algebraic space, read on the acted-on presheaf

`AlgebraicGeometry.Space.objectOverStarModObj` turns an action of a presheaf of groups `F` on a
presheaf `P` over the big fppf site over `S` into an action of `G_B = B ×_S G` on `X_B = B ×_S X`
in the slice of presheaves over `B`, by transporting it along the monoidal functor
`AlgebraicGeometry.Space.overStar`. This file computes the resulting action morphism back in terms
of the original one.

The slice `CategoryTheory.Over B` is cartesian monoidal through pullbacks, so the source of the
transported action is `pullback (B ⨯ F).hom (B ⨯ P).hom` — the pairs of a point of `B ⨯ F` and a
point of `B ⨯ P` with the same image in `B` — and the transported action is the lax monoidal
comparison `CategoryTheory.Functor.LaxMonoidal.μ` of `overStar` followed by the image of the
original action. Both are pinned by their components along the two projections, and that is what
the three lemmas below record: the `B`-component of the action morphism is forced, being a morphism
over `B`, and its `P`-component is the original action applied to the `F`-component of the first
factor and the `P`-component of the second.

Over a *terminal* base the `B`-component carries no information, and the second projection
`B ⨯ Q ⟶ Q` is an isomorphism; that unitor is recorded here too, since the quotient stack `[X/G]`
of a group action on the site is the one taken over the base itself.

## Main definitions

* `AlgebraicGeometry.Space.terminalSpaceProdIso`: the unitor `B ⨯ Q ≅ Q` at the terminal base.

## Main results

* `CategoryTheory.Functor.LaxMonoidal.modObj_smul`: the action morphism of a transported module
  structure, as an equation rather than a definitional unfolding.
* `AlgebraicGeometry.Space.overStar_map_left` and
  `AlgebraicGeometry.Space.overStar_obj_hom`: the underlying presheaf and structure morphism of
  `AlgebraicGeometry.Space.overStar`.
* `AlgebraicGeometry.Space.mu_overStar_left_comp_snd`: the lax monoidal comparison of `overStar`,
  read on the acted-on presheaf.
* `AlgebraicGeometry.Space.smul_objectOverStar_left_comp_snd`: **the transported action, read on
  the acted-on presheaf**: the pair of the group component of the first factor and the object
  component of the second, fed to the original action.
* `AlgebraicGeometry.Space.isIso_prod_snd_terminalSpace`: the second projection out of a product
  with the terminal presheaf is an isomorphism.

## Implementation notes

Everything is proved in term mode. The underlying presheaf of `(overStar B).obj Q` is `B ⨯ Q` by
`rfl` but not syntactically, so a goal mentioning both `((overStar B).obj Q).left` and `B ⨯ Q` is
type-correct only at default transparency and `rw` refuses it with "the target expression is not
type-correct under the 'implicit' transparency level"; `congrArg` and `Category.assoc` applied as
terms are not affected, and the `backward.isDefEq.respectTransparency` option, which Mathlib
reaches for in the analogous lemmas for `CategoryTheory.Over.pullback`, is then not needed.

`CategoryTheory.Functor.LaxMonoidal.modObj_smul` is stated here rather than beside
`CategoryTheory.Functor.LaxMonoidal.modObj` in
`StacksFrontier/AlgebraicGeometry/Groupoids/Stabilizer/ModObj.lean`, so that this file adds no
declaration to a module another file already owns. It is needed because the action morphism of
`AlgebraicGeometry.Space.objectOverStarModObj` cannot be unfolded by `rfl` inside a goal: the
whole term exhausts the elaborator's budget, while the single projection out of the structure
does not.

## References

* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v w

namespace CategoryTheory.Functor.LaxMonoidal

/-- **The action morphism of a transported module structure.** It is the lax monoidal comparison
of the functor followed by the image of the original action morphism. This is the defining
equation of `CategoryTheory.Functor.LaxMonoidal.modObj`, stated so that a consumer need not
unfold it. -/
theorem modObj_smul {C D : Type*} [Category.{v} C] [MonoidalCategory C]
    [Category.{w} D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {M X : C} [MonObj M] [ModObj M X] (M' : MonObj (F.obj M))
    (hone : Functor.LaxMonoidal.ε F ≫ F.map η[M] = M'.one)
    (hmul : Functor.LaxMonoidal.μ F M M ≫ F.map μ[M] = M'.mul) :
    (modObj F M' hone hmul).smul =
      Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] := rfl

end CategoryTheory.Functor.LaxMonoidal

namespace AlgebraicGeometry.Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)
  (Bo : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)

/-! ### The functor `B ⨯ -` into the slice -/

/-- `AlgebraicGeometry.Space.overStar` acts on a morphism by the identity on `B` and the morphism
on the second factor. -/
theorem overStar_map_left {Q R : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (f : Q ⟶ R) :
    ((overStar 𝒞 S hS Bo).map f).left = prod.map (𝟙 Bo) f := rfl

/-- The structure morphism of `B ⨯ Q` over `B` is the first projection. It is *not* that morphism
on the nose: `CategoryTheory.Over.star` builds it as the first projection of the comonad's
counit, which is the first projection only after `CategoryTheory.Limits.prod.lift_fst`. -/
theorem overStar_obj_hom (Q : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    ((overStar 𝒞 S hS Bo).obj Q).hom = (prod.fst : Bo ⨯ Q ⟶ Bo) := by
  change prod.lift prod.fst (𝟙 _) ≫ prod.fst = _
  exact prod.lift_fst _ _

/-! ### The lax monoidal comparison of `B ⨯ -` -/

/-- Reading `μ ≫ overStar.map z` on the second factor is the second-factor component of `μ`
followed by `z`. -/
private theorem mu_left_comp_snd_comp {Q R T : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (z : Q ⊗ R ⟶ T) (w : (overStar 𝒞 S hS Bo).obj Q ⊗ (overStar 𝒞 S hS Bo).obj R ⟶
      (overStar 𝒞 S hS Bo).obj T)
    (hw : Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) Q R ≫ (overStar 𝒞 S hS Bo).map z = w) :
    (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) Q R).left ≫ prod.snd ≫ z = w.left ≫ prod.snd :=
  (congrArg (fun y : (Bo ⨯ (Q ⊗ R)) ⟶ T =>
      (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) Q R).left ≫ y)
    (prod.map_snd (𝟙 Bo) z).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun y : (overStar 𝒞 S hS Bo).obj Q ⊗ (overStar 𝒞 S hS Bo).obj R ⟶
            (overStar 𝒞 S hS Bo).obj T => y.left ≫ prod.snd) hw))

/-- The group component of the lax monoidal comparison of `AlgebraicGeometry.Space.overStar` is
the group component of the first factor. -/
theorem mu_overStar_left_comp_snd_fst (Q R : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) Q R).left ≫ prod.snd ≫ fst Q R =
      pullback.fst ((overStar 𝒞 S hS Bo).obj Q).hom ((overStar 𝒞 S hS Bo).obj R).hom ≫
        prod.snd :=
  mu_left_comp_snd_comp 𝒞 S hS Bo _ _ (Functor.Monoidal.μ_fst (overStar 𝒞 S hS Bo) Q R)

/-- The object component of the lax monoidal comparison of `AlgebraicGeometry.Space.overStar` is
the object component of the second factor. -/
theorem mu_overStar_left_comp_snd_snd (Q R : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) Q R).left ≫ prod.snd ≫ snd Q R =
      pullback.snd ((overStar 𝒞 S hS Bo).obj Q).hom ((overStar 𝒞 S hS Bo).obj R).hom ≫
        prod.snd :=
  mu_left_comp_snd_comp 𝒞 S hS Bo _ _ (Functor.Monoidal.μ_snd (overStar 𝒞 S hS Bo) Q R)

/-- **The lax monoidal comparison of `AlgebraicGeometry.Space.overStar`, read on the second
factor.** It pairs the second components of the two factors of the pullback. -/
theorem mu_overStar_left_comp_snd (Q R : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) Q R).left ≫ prod.snd =
      lift (pullback.fst ((overStar 𝒞 S hS Bo).obj Q).hom
            ((overStar 𝒞 S hS Bo).obj R).hom ≫ prod.snd)
        (pullback.snd ((overStar 𝒞 S hS Bo).obj Q).hom
          ((overStar 𝒞 S hS Bo).obj R).hom ≫ prod.snd) :=
  CartesianMonoidalCategory.hom_ext _ _
    ((Category.assoc _ _ _).trans
      ((mu_overStar_left_comp_snd_fst 𝒞 S hS Bo Q R).trans (lift_fst _ _).symm))
    ((Category.assoc _ _ _).trans
      ((mu_overStar_left_comp_snd_snd 𝒞 S hS Bo Q R).trans (lift_snd _ _).symm))

/-! ### The transported action -/

variable (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u})
  (P : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) [ModObj (F ⋙ forget GrpCat) P]

/-- **The transported action is the lax monoidal comparison followed by the image of the original
action.** -/
theorem smul_objectOverStar :
    γ[groupOverStar 𝒞 S hS Bo F, objectOverStar 𝒞 S hS Bo P] =
      Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) (F ⋙ forget GrpCat) P ≫
        (overStar 𝒞 S hS Bo).map γ[F ⋙ forget GrpCat, P] :=
  Functor.LaxMonoidal.modObj_smul (overStar 𝒞 S hS Bo) _ rfl rfl

/-- The underlying morphism of presheaves of the transported action. -/
theorem smul_objectOverStar_left :
    γ[groupOverStar 𝒞 S hS Bo F, objectOverStar 𝒞 S hS Bo P].left =
      (Functor.LaxMonoidal.μ (overStar 𝒞 S hS Bo) (F ⋙ forget GrpCat) P).left ≫
        prod.map (𝟙 Bo) γ[F ⋙ forget GrpCat, P] :=
  (congrArg (fun z : groupOverStar 𝒞 S hS Bo F ⊗ objectOverStar 𝒞 S hS Bo P ⟶
      objectOverStar 𝒞 S hS Bo P => z.left) (smul_objectOverStar 𝒞 S hS Bo F P)).trans
    (Over.comp_left _ _ _ _ _)

/-- **The transported action, read on the acted-on presheaf.** A point of the source is a pair of
a point of `B ⨯ G` and a point of `B ⨯ X` over the same point of `B`; the action sends it to the
value of the original action on the group component of the first and the object component of the
second. -/
theorem smul_objectOverStar_left_comp_snd :
    γ[groupOverStar 𝒞 S hS Bo F, objectOverStar 𝒞 S hS Bo P].left ≫
        (prod.snd : Bo ⨯ P ⟶ P) =
      lift (pullback.fst ((overStar 𝒞 S hS Bo).obj (F ⋙ forget GrpCat)).hom
              ((overStar 𝒞 S hS Bo).obj P).hom ≫ prod.snd)
          (pullback.snd ((overStar 𝒞 S hS Bo).obj (F ⋙ forget GrpCat)).hom
            ((overStar 𝒞 S hS Bo).obj P).hom ≫ prod.snd) ≫
        γ[F ⋙ forget GrpCat, P] :=
  ((mu_left_comp_snd_comp 𝒞 S hS Bo γ[F ⋙ forget GrpCat, P] _
    (smul_objectOverStar 𝒞 S hS Bo F P).symm).symm.trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z : (groupOverStar 𝒞 S hS Bo F ⊗ objectOverStar 𝒞 S hS Bo P).left ⟶
            (F ⋙ forget GrpCat) ⊗ P => z ≫ γ[F ⋙ forget GrpCat, P])
          (mu_overStar_left_comp_snd 𝒞 S hS Bo (F ⋙ forget GrpCat) P))))

/-! ### The unitor at the terminal base -/

/-- **The second projection out of a product with the terminal presheaf is an isomorphism.** The
presheaf represented by the base scheme is the final presheaf on the big fppf site over `S`, and a
binary fan whose first leg has a terminal vertex is a limit exactly when its second leg is an
isomorphism. -/
theorem isIso_prod_snd_terminalSpace (Q : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    IsIso (prod.snd : (terminalSpace 𝒞 S hS).obj ⨯ Q ⟶ Q) :=
  (CategoryTheory.Limits.BinaryFan.isLimit_iff_isIso_snd
    (AlgebraicGeometry.Space.baseTerminal_yonedaIsTerminal 𝒞 S hS) _).1 ⟨limit.isLimit _⟩

/-- The unitor of the terminal base: `B ⨯ Q ≅ Q`, the second projection. -/
noncomputable def terminalSpaceProdIso (Q : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    (terminalSpace 𝒞 S hS).obj ⨯ Q ≅ Q :=
  haveI := isIso_prod_snd_terminalSpace 𝒞 S hS Q
  asIso (prod.snd : (terminalSpace 𝒞 S hS).obj ⨯ Q ⟶ Q)

/-- The unitor of the terminal base is the second projection. -/
theorem terminalSpaceProdIso_hom (Q : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    (terminalSpaceProdIso 𝒞 S hS Q).hom = prod.snd := rfl

end AlgebraicGeometry.Space

end
