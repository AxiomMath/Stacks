module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech complex of an abelian presheaf as maps out of the integral Čech complex

Let `E = {U_i → U}` be a family of morphisms of a category `C` with fixed target, all of whose
finite nonempty fibre products exist, and let `F` be an abelian presheaf on `C`. Stacks 03OL
defines the Čech complex of `E` and `F`; Stacks 03OP writes it out explicitly as the complex of
maps out of the integral Čech complex of Stacks 03AS,
`Hom(⊕_{i₀} ℤ_{U_{i₀}} ← ⊕_{i₀i₁} ℤ_{U_{i₀} ×_U U_{i₁}} ← ⋯, F)`, whose degree-`p` term is
`∏_{i₀ ⋯ i_p} Hom(ℤ_{U_{i₀} ×_U ⋯ ×_U U_{i_p}}, F)` and whose differential is the alternating
sum of the maps repeating one of the indices.

Stacks 03OP is the étale-cohomology chapter's restatement, for abelian presheaves on a
category, of the Hom identification of Stacks 03AS, which this library already proves as
`Stacks.CechSite.homIntegralCechComplexIso`. What this file adds is the degreewise product of
`Hom`-groups -- the first of the two displays of 03OP, which Stacks 03AS uses only inside the
proof of its Hom identification -- and the form of the identification for the Čech complex of
`F` itself rather than of a universe lift of `F`.

## Main definitions

* `Stacks.CechSite.homCoproductIsoProduct`: maps out of a coproduct of abelian presheaves are
  a family of maps out of the summands.

## Main results

* `Stacks.CechSite.homIntegralCechComplex_d`,
  `Stacks.CechSite.cechComplexIsoHomIntegralCechComplex`,
  `Stacks.CechSite.homIntegralCechComplexXIso` and
  `Stacks.CechSite.cechComplexIsoHomIntegralCechComplexObj`: **Stacks 03OP**, the differential
  of the complex of maps out of the integral Čech complex, the identification of that complex
  with the Čech complex, and its degree-`p` term as a product of `Hom`-groups.

## Implementation notes

A family of morphisms with fixed target is a `CategoryTheory.PreZeroHypercover`, as in Stacks
03OL, and the fibre products are products in the over category.

The degree-`p` term is a product, indexed by a type in the family's index universe `w`, of
objects of `AddCommGrpCat` in the universe `max u v a` in which morphisms of abelian presheaves
live. Those universes are independent, so the product is available only from the hypothesis
`HasProducts.{w} AddCommGrpCat.{max u v a}` which the Čech complex of Stacks 03AM already
carries, and it is written with its type ascribed: without the ascription the coefficient
universe of the family is still a metavariable when the `HasProduct` instance is synthesized,
instance search reaches for the `UnivLE`-conditioned instance on `AddCommGrpCat` instead of the
hypothesis, and the declaration fails with an unsolved universe constraint
`max u v a =?= max u v w a`.

Because the groups of maps of abelian presheaves live in the universe `max u v a` while the
values of a presheaf live in `max v a`, the identification of Stacks 03AS compares the complex
of maps out of the integral Čech complex with the Čech complex of the universe lift of `F`.
`Stacks.CechSite.cechComplexIsoHomIntegralCechComplexObj` removes that lift by pinning the
coefficient universe to contain `u`, which is the pinning already used for Stacks 03OR.

## References

* [Stacks Project, Tag 03OP](https://stacks.math.columbia.edu/tag/03OP)
* [Stacks Project, Tag 03OL](https://stacks.math.columbia.edu/tag/03OL)
* [Stacks Project, Tag 03AS](https://stacks.math.columbia.edu/tag/03AS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

/-- An additive contravariant functor turns an alternating sum of morphisms into the
alternating sum of their images. -/
theorem map_op_sum_zsmul {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    (G : Aᵒᵖ ⥤ B) [G.Additive] {ι : Type*} [Fintype ι] {Y Z : A}
    (c : ι → ℤ) (g : ι → (Y ⟶ Z)) :
    G.map (∑ j, c j • g j).op = ∑ j, c j • G.map (g j).op := by
  simp only [op_sum, op_zsmul, Functor.map_sum, Functor.map_zsmul]

end CategoryTheory.Functor

namespace Stacks.CechSite

section ExplicitDescription

universe w v u a t

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

/-- Maps out of a coproduct of abelian presheaves are the same thing as a family of maps out of
the summands. -/
noncomputable def homCoproductIsoProduct {J : Type w}
    (G : J → (Cᵒᵖ ⥤ AddCommGrpCat.{t})) [HasCoproduct G]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    [HasProduct (fun j ↦ AddCommGrpCat.of (G j ⟶ F))] :
    AddCommGrpCat.of ((∐ G) ⟶ F) ≅ ∏ᶜ (fun j ↦ AddCommGrpCat.of (G j ⟶ F)) where
  hom := Pi.lift fun j ↦ AddCommGrpCat.ofHom
    { toFun := fun f ↦ Sigma.ι G j ≫ f
      map_zero' := by simp
      map_add' := by simp }
  inv := AddCommGrpCat.ofHom
    { toFun := fun x ↦ Sigma.desc fun j ↦ Pi.π (fun j ↦ AddCommGrpCat.of (G j ⟶ F)) j x
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  hom_inv_id := by ext f j; simp
  inv_hom_id := by ext x j; simp

variable [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- **Stacks 03OP.** The differential of the complex of maps out of the integral Čech complex is
the alternating sum of the maps induced by the face maps of the simplicial formal coproduct of
fibre products, that is, of the maps which repeat one of the indices. -/
@[stacks 03OP "the differential"]
theorem homIntegralCechComplex_d (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (n : ℕ) :
    ((homComplexFunctor (integralCechComplex.{w, v, u, a} E)).obj F).d n (n + 1) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (preadditiveYoneda.obj F).map
          ((integralCechRealization.{w, v, u, a} (X := X)).map
            ((cechSimplicialObject E).δ j)).op := by
  have hd : (integralCechComplex.{w, v, u, a} E).d (n + 1) n =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (integralCechRealization.{w, v, u, a} (X := X)).map
          ((cechSimplicialObject E).δ j) := integralCechComplex_d.{w, v, u, a} E n
  show (preadditiveYoneda.obj F).map
    ((integralCechComplex.{w, v, u, a} E).d (n + 1) n).op = _
  rw [hd]
  exact (preadditiveYoneda.obj F).map_op_sum_zsmul _ _

variable [HasProducts.{w} AddCommGrpCat.{max u v a}]

/-- **Stacks 03OP.** The Čech complex of an abelian presheaf `F` is the complex of maps out of
the integral Čech complex of Stacks 03OQ, naturally in `F`. This is the second of the two
displays of 03OP, and it is the Hom identification of Stacks 03AS; the values of the Čech
complex are lifted to the universe in which maps of abelian presheaves live. -/
@[stacks 03OP "the identification of the Čech complex with maps out of the integral complex"]
noncomputable def cechComplexIsoHomIntegralCechComplex :
    liftedCechComplexFunctor.{w, v, u, a} E ≅
      homComplexFunctor (integralCechComplex.{w, v, u, a} E) :=
  (homIntegralCechComplexIso.{w, v, u, a} E).symm

/-- **Stacks 03OP.** The degree-`n` term of the complex of maps out of the integral Čech complex
is the product, over `(n+1)`-tuples `i` of indices, of the groups of maps from the free abelian
presheaf on the fibre product `U_{i 0} ×_U ⋯ ×_U U_{i n}` to `F`. This is the first of the two
displays of 03OP. -/
@[stacks 03OP "the degreewise product of Hom-groups"]
noncomputable def homIntegralCechComplexXIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) (n : ℕ) :
    ((homComplexFunctor (integralCechComplex.{w, v, u, a} E)).obj F).X n ≅
      ((∏ᶜ (fun i : Fin (n + 1) → E.I₀ ↦ AddCommGrpCat.of
        (freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left) ⟶ F)) :
          AddCommGrpCat.{max u v a})) :=
  homCoproductIsoProduct
    (fun i : Fin (n + 1) → E.I₀ ↦
      freeAbelianYoneda.{v, u, a}.obj ((∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left)) F

end ExplicitDescription

section ExplicitDescriptionUnlifted

universe w v u a

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max u v a})]
  [HasProducts.{w} AddCommGrpCat.{max u v a}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- **Stacks 03OP.** When the coefficient universe contains the universe of objects of `C`, so
that the groups of maps of abelian presheaves lie in the coefficient universe too, the Čech
complex of `F` itself -- and not merely a universe lift of it -- is the complex of maps out of
the integral Čech complex. -/
@[stacks 03OP "the identification for the Čech complex itself"]
noncomputable def cechComplexIsoHomIntegralCechComplexObj
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v a}) :
    cechComplex E F ≅
      (homComplexFunctor (integralCechComplex.{w, v, u, max u a} E)).obj F :=
  let η : F ≅ F ⋙ AddCommGrpCat.uliftFunctor.{u, max v (max u a)} :=
    NatIso.ofComponents (fun _ ↦ AddEquiv.ulift.symm.toAddCommGrpIso)
      (by intro U V f; ext x; rfl)
  (cechComplexFunctor E).mapIso η ≪≫
    ((homIntegralCechComplexIso.{w, v, u, max u a} E).app F).symm

end ExplicitDescriptionUnlifted

end Stacks.CechSite

end
