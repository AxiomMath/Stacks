module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormula.CommaNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormula.LanNaturality

/-!
# The sum formula of Stacks 09WG (6) as a natural isomorphism

Let `Cs` be a simplicial site — case (A) of the simplicial-site situation of Stacks 09WE — and
let `ι_k` denote the inclusion of its degree-`k` component into the total category. Stacks
09WG (6) says that the restriction to the degree-`m` component of the abelian lower shriek of a
sheaf on the degree-`n` component is the direct sum, over the simplex maps `ψ : [n] → [m]`, of
its inverse images along the transition functors.

`Stacks.Sites.AbelianSumFormula.lanObjObjSumIso` is that formula at the level of presheaves and
at one object of the degree-`m` component. This file gives it as a morphism of functors: for
each `ψ` a natural transformation from the left Kan extension along the transition functor `u_ψ`
to the restriction along `ι_m` of the left Kan extension along `ι_n`, whose induced morphism out
of the coproduct over `ψ` is an isomorphism at every presheaf.

## Main results

* `Stacks.Sites.ComponentSumFormula.sumInclusionApp`: the comparison map at one object.
* `Stacks.Sites.ComponentSumFormula.sumInclusionApp_naturality_object` and
  `Stacks.Sites.ComponentSumFormula.sumInclusionApp_naturality_presheaf`: it is natural in the
  base object and in the presheaf.
* `Stacks.Sites.ComponentSumFormula.lanSumInclusion`: the comparison as a morphism of functors.
* `Stacks.Sites.ComponentSumFormula.isIso_sigmaDesc_lanSumInclusion`: the sum formula of
  Stacks 09WG (6): the induced morphism out of the coproduct over the simplex maps is an
  isomorphism at every presheaf.

## Implementation notes

The three lemmas of the `Pasting` section do the composition algebra of the two naturality proofs
in an abstract category, where the morphisms are variables. The goals of those proofs mention
objects of the total category in the `{base := op m, fiber := W}` spelling, on which
`rw [Category.assoc]` fails; applying the abstract lemmas with `exact`, which checks at default
transparency, avoids this. For the same reason `colimit_pre_eq_of_functor_eq` is a lemma rather
than a `rw`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open Stacks.Sites.AbelianSumFormula

universe v u

namespace Stacks.Sites.ComponentSumFormula

section Pasting

variable {A : Type v} [Category.{u} A]

/-- A commuting square whose vertical legs are isomorphisms can be read with those legs
inverted. -/
theorem inv_square_of_square {X Y X' Y' : A} (e : X ≅ Y) (e' : X' ≅ Y') {w : X ⟶ X'}
    {z : Y ⟶ Y'} (h : w ≫ e'.hom = e.hom ≫ z) : z ≫ e'.inv = e.inv ≫ w := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Pasting two commuting squares side by side. -/
theorem comp_eq_comp_of_two_squares {X X' Y Y' Z Z' : A} {uu : X ⟶ X'} {cc : Z ⟶ Z'}
    {a : X ⟶ Y} {a' : X' ⟶ Y'} {q : Y ⟶ Y'} {bi : Y ⟶ Z} {bi' : Y' ⟶ Z'}
    (hA : uu ≫ a' = a ≫ q) (hB : q ≫ bi' = bi ≫ cc) :
    uu ≫ a' ≫ bi' = (a ≫ bi) ≫ cc := by
  rw [← Category.assoc, hA, Category.assoc, hB, Category.assoc]

/-- Pasting three commuting squares side by side. -/
theorem comp_eq_comp_of_three_squares {X X' Y Y' Z Z' T T' : A} {uu : X ⟶ X'} {vv : T ⟶ T'}
    {a : X ⟶ Y} {a' : X' ⟶ Y'} {q₁ : Y ⟶ Y'} {p : Y ⟶ Z} {p' : Y' ⟶ Z'} {q₂ : Z ⟶ Z'}
    {bi : Z ⟶ T} {bi' : Z' ⟶ T'}
    (hA : uu ≫ a' = a ≫ q₁) (hC : q₁ ≫ p' = p ≫ q₂) (hB : q₂ ≫ bi' = bi ≫ vv) :
    uu ≫ a' ≫ p' ≫ bi' = (a ≫ p ≫ bi) ≫ vv := by
  rw [← Category.assoc, hA, Category.assoc, Category.assoc, ← Category.assoc q₁, hC,
    Category.assoc, Category.assoc, hB]

end Pasting

variable {A : Type v} [Category.{u} A] [HasColimitsOfSize.{u, u} A]

/-- **The reindexing map of a colimit depends on the reindexing functor only up to transport.** -/
theorem colimit_pre_eq_of_functor_eq {I K : Type u} [SmallCategory I] [SmallCategory K]
    (F : K ⥤ A) {E E' : I ⥤ K} (h : E = E') :
    colimit.pre F E =
      eqToHom (congrArg (fun D : I ⥤ K => colimit (D ⋙ F)) h) ≫ colimit.pre F E' := by
  subst h; simp

/-- **The comma-category description of a left Kan extension's values is natural in the
presheaf**, over the structured arrows of `L`. -/
theorem lanObjObjIsoColimit_naturality_presheaf {C D : Type u} [SmallCategory C] [SmallCategory D]
    (L : C ⥤ D) {P Q : Cᵒᵖ ⥤ A} (β : P ⟶ Q) (V : D) :
    (L.op.lan.map β).app (op V) ≫ (lanObjObjIsoColimit L Q V).hom =
      (lanObjObjIsoColimit L P V).hom ≫
        colimMap (Functor.whiskerLeft (StructuredArrow.proj V L).op β) := by
  have hA := Stacks.PresheafOfModules.Pullback.lke_morphism_naturality L.op β (op V)
  have hC := colimit.pre_map (G := CostructuredArrow.proj L.op (op V) ⋙ P)
    (F := CostructuredArrow.proj L.op (op V) ⋙ Q)
    (Functor.whiskerLeft (CostructuredArrow.proj L.op (op V)) β)
    (structuredArrowOpEquivalence L V).functor
  have hB := inv_square_of_square
    (Functor.Final.colimitIso (structuredArrowOpEquivalence L V).functor
      (CostructuredArrow.proj L.op (op V) ⋙ P))
    (Functor.Final.colimitIso (structuredArrowOpEquivalence L V).functor
      (CostructuredArrow.proj L.op (op V) ⋙ Q))
    (by rw [Functor.Final.colimitIso_hom, Functor.Final.colimitIso_hom]; exact hC.symm)
  show (L.op.lan.map β).app (op V) ≫
      ((L.op.leftKanExtensionObjIsoColimit Q (op V)).hom ≫
        (Functor.Final.colimitIso (structuredArrowOpEquivalence L V).functor
          (CostructuredArrow.proj L.op (op V) ⋙ Q)).inv) =
    ((L.op.leftKanExtensionObjIsoColimit P (op V)).hom ≫
        (Functor.Final.colimitIso (structuredArrowOpEquivalence L V).functor
          (CostructuredArrow.proj L.op (op V) ⋙ P)).inv) ≫
      colimMap (Functor.whiskerLeft (StructuredArrow.proj V L).op β)
  exact comp_eq_comp_of_two_squares hA hB

variable {Cs : SimplicialSite.{u}} {m n : SimplexCategory}

/-- **The two reindexing maps of the summand decomposition commute.** For a morphism
`f : W' ⟶ W` of the degree-`m` component, reindexing a colimit over the comma category of the
component inclusion along the `ψ`-summand inclusion and along precomposition with `f` commute. -/
theorem colimit_pre_summandInclusion_comm (ψ : n ⟶ m) (P : (Cs.underlying.obj n)ᵒᵖ ⥤ A)
    {W W' : Cs.underlying.obj m} (f : W' ⟶ W) :
    colimit.pre ((StructuredArrow.proj W' (Cs.underlying.map ψ).toFunctor).op ⋙ P)
        (StructuredArrow.map (T := (Cs.underlying.map ψ).toFunctor) f).op ≫
      colimit.pre ((StructuredArrow.proj (⟨op m, W'⟩ : CoGrothendieck Cs.totalPseudofunctor)
          (CoGrothendieck.ι Cs.totalPseudofunctor (op n))).op ⋙ P)
        (summandInclusion (W := W') ψ).op =
    colimit.pre ((StructuredArrow.proj (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
          (CoGrothendieck.ι Cs.totalPseudofunctor (op n))).op ⋙ P)
        (summandInclusion (W := W) ψ).op ≫
      colimit.pre ((StructuredArrow.proj (⟨op m, W'⟩ : CoGrothendieck Cs.totalPseudofunctor)
          (CoGrothendieck.ι Cs.totalPseudofunctor (op n))).op ⋙ P)
        (StructuredArrow.map ((CoGrothendieck.ι Cs.totalPseudofunctor (op m)).map f)).op := by
  have h := summandInclusion_op_comp_structuredArrowMap_op (Cs := Cs) (W := W) (W' := W') ψ f
  let F := (StructuredArrow.proj (⟨op m, W'⟩ : CoGrothendieck Cs.totalPseudofunctor)
    (CoGrothendieck.ι Cs.totalPseudofunctor (op n))).op ⋙ P
  exact (colimit.pre_pre F (summandInclusion (W := W') ψ).op
      (StructuredArrow.map (T := (Cs.underlying.map ψ).toFunctor) f).op).trans
    (((colimit_pre_eq_of_functor_eq F h).trans (Category.id_comp _)).symm.trans
      (colimit.pre_pre F (StructuredArrow.map
        ((CoGrothendieck.ι Cs.totalPseudofunctor (op m)).map f)).op
        (summandInclusion (W := W) ψ).op).symm)

/-- **The sum formula's comparison map at one object.** For a simplex map `ψ : n ⟶ m` and an
object `W` of the degree-`m` component, the map from the value at `W` of the left Kan extension
along the transition functor `u_ψ` to the value at `(m, W)` of the left Kan extension along the
degree-`n` component inclusion: read both as colimits over comma categories and reindex along the
`ψ`-summand inclusion. -/
noncomputable def sumInclusionApp (ψ : n ⟶ m) (P : (Cs.underlying.obj n)ᵒᵖ ⥤ A)
    (W : Cs.underlying.obj m) :
    ((Cs.underlying.map ψ).toFunctor.op.lan.obj P).obj (op W) ⟶
      ((CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan.obj P).obj
        (op (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)) :=
  (lanObjObjIsoColimit (Cs.underlying.map ψ).toFunctor P W).hom ≫
    colimit.pre ((StructuredArrow.proj (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
        (CoGrothendieck.ι Cs.totalPseudofunctor (op n))).op ⋙ P)
      (summandInclusion (W := W) ψ).op ≫
    (lanObjObjIsoColimit (CoGrothendieck.ι Cs.totalPseudofunctor (op n)) P
      (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)).inv

/-- **The comparison map is natural in the base object.** -/
theorem sumInclusionApp_naturality_object (ψ : n ⟶ m) (P : (Cs.underlying.obj n)ᵒᵖ ⥤ A)
    {W W' : Cs.underlying.obj m} (f : W' ⟶ W) :
    ((Cs.underlying.map ψ).toFunctor.op.lan.obj P).map f.op ≫ sumInclusionApp ψ P W' =
      sumInclusionApp ψ P W ≫
        ((CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan.obj P).map
          ((CoGrothendieck.ι Cs.totalPseudofunctor (op m)).map f).op :=
  comp_eq_comp_of_three_squares
    (lanObjObjIsoColimit_naturality (Cs.underlying.map ψ).toFunctor P f)
    (colimit_pre_summandInclusion_comm ψ P f)
    (inv_square_of_square _ _
      (lanObjObjIsoColimit_naturality (CoGrothendieck.ι Cs.totalPseudofunctor (op n)) P
        ((CoGrothendieck.ι Cs.totalPseudofunctor (op m)).map f)))

/-- **The comparison map is natural in the presheaf.** -/
theorem sumInclusionApp_naturality_presheaf (ψ : n ⟶ m)
    {P Q : (Cs.underlying.obj n)ᵒᵖ ⥤ A} (β : P ⟶ Q) (W : Cs.underlying.obj m) :
    ((Cs.underlying.map ψ).toFunctor.op.lan.map β).app (op W) ≫ sumInclusionApp ψ Q W =
      sumInclusionApp ψ P W ≫
        ((CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan.map β).app
          (op (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)) :=
  comp_eq_comp_of_three_squares
    (lanObjObjIsoColimit_naturality_presheaf (Cs.underlying.map ψ).toFunctor β W)
    (colimit.pre_map (Functor.whiskerLeft
        (StructuredArrow.proj (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
          (CoGrothendieck.ι Cs.totalPseudofunctor (op n))).op β)
      (summandInclusion (W := W) ψ).op).symm
    (inv_square_of_square _ _
      (lanObjObjIsoColimit_naturality_presheaf
        (CoGrothendieck.ι Cs.totalPseudofunctor (op n)) β
        (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)))

/-- **The sum formula's comparison map, as a morphism of functors.** For a simplex map
`ψ : n ⟶ m`, the natural transformation from the left Kan extension along the transition functor
`u_ψ` to the restriction along the degree-`m` component inclusion of the left Kan extension along
the degree-`n` component inclusion. -/
noncomputable def lanSumInclusion (ψ : n ⟶ m) :
    ((Cs.underlying.map ψ).toFunctor.op.lan :
        ((Cs.underlying.obj n)ᵒᵖ ⥤ A) ⥤ ((Cs.underlying.obj m)ᵒᵖ ⥤ A)) ⟶
      (CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan ⋙
        (Functor.whiskeringLeft _ _ A).obj
          (CoGrothendieck.ι Cs.totalPseudofunctor (op m)).op where
  app P :=
    { app := fun X => sumInclusionApp ψ P X.unop
      naturality := fun _ _ g => sumInclusionApp_naturality_object ψ P g.unop }
  naturality _ _ β := by
    ext X
    exact sumInclusionApp_naturality_presheaf ψ β X.unop

/-- The coproduct descent of the comparison maps at one object is the objectwise sum formula
`Stacks.Sites.AbelianSumFormula.lanObjObjSumIso`. -/
theorem sigmaDesc_sumInclusionApp [HasColimitsOfShape (Discrete (n ⟶ m)) A]
    (W : Cs.underlying.obj m) (P : (Cs.underlying.obj n)ᵒᵖ ⥤ A) :
    (Limits.Sigma.desc fun ψ : n ⟶ m => sumInclusionApp ψ P W) =
      (lanObjObjSumIso (W := W) P).hom := by
  refine Limits.Sigma.hom_ext _ _ fun ψ => ?_
  refine (Limits.Sigma.ι_desc _ ψ).trans
    (Eq.symm ((Limits.Sigma.ι_mapIso_hom_assoc _ ψ _).trans ?_))
  exact congrArg (fun z => (lanObjObjIsoColimit (Cs.underlying.map ψ).toFunctor P W).hom ≫ z)
    (Limits.Sigma.ι_desc_assoc _ ψ _)

/-- **The sum formula of Stacks 09WG (6), as a natural isomorphism.** The morphism induced out of
the coproduct over the simplex maps `ψ : n ⟶ m` by the comparison maps
`Stacks.Sites.ComponentSumFormula.lanSumInclusion` is an isomorphism of presheaves on the
degree-`m` component, at every presheaf on the degree-`n` component. -/
theorem isIso_sigmaDesc_lanSumInclusion [HasColimitsOfShape (Discrete (n ⟶ m)) A]
    (P : (Cs.underlying.obj n)ᵒᵖ ⥤ A) :
    IsIso (Limits.Sigma.desc fun ψ : n ⟶ m =>
      (lanSumInclusion (A := A) (Cs := Cs) (m := m) (n := n) ψ).app P) := by
  have key : ∀ X : ((Cs.underlying.obj m)ᵒᵖ), IsIso ((Limits.Sigma.desc fun ψ : n ⟶ m =>
      (lanSumInclusion (A := A) (Cs := Cs) (m := m) (n := n) ψ).app P).app X) := by
    rintro ⟨W⟩
    have hd := sigmaComparison_map_desc ((evaluation ((Cs.underlying.obj m)ᵒᵖ) A).obj (op W))
      (fun ψ : n ⟶ m => (Cs.underlying.map ψ).toFunctor.op.lan.obj P) _
      (fun ψ : n ⟶ m => (lanSumInclusion (A := A) (Cs := Cs) (m := m) (n := n) ψ).app P)
    have heq : (Limits.Sigma.desc fun ψ : n ⟶ m =>
          ((evaluation ((Cs.underlying.obj m)ᵒᵖ) A).obj (op W)).map
            ((lanSumInclusion (A := A) (Cs := Cs) (m := m) (n := n) ψ).app P)) =
        (lanObjObjSumIso (W := W) P).hom :=
      sigmaDesc_sumInclusionApp W P
    have hiso : IsIso (Limits.Sigma.desc fun ψ : n ⟶ m =>
        ((evaluation ((Cs.underlying.obj m)ᵒᵖ) A).obj (op W)).map
          ((lanSumInclusion (A := A) (Cs := Cs) (m := m) (n := n) ψ).app P)) := by
      rw [heq]; exact Iso.isIso_hom _
    exact IsIso.of_isIso_fac_left hd
  exact NatIso.isIso_of_isIso_app _

end Stacks.Sites.ComponentSumFormula

end
