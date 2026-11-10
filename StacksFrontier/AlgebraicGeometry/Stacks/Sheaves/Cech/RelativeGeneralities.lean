module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.Complex
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# Generalities on relative Čech complexes

A `2`-commutative square of categories fibred in groupoids over a base category induces, in
each Čech degree, a `1`-morphism of relative Čech nerves, hence a base-change morphism
`e⁻¹𝒦^•(f, F) ⟶ 𝒦^•(g, e⁻¹F)` of complexes of abelian presheaves. That morphism is an
isomorphism as soon as the two horizontal `1`-morphisms of the square are equivalences, and
`2`-isomorphic `1`-morphisms have isomorphic relative Čech complexes.

## Main definitions

* `Stacks.RelativeCech.baseChangeComponent`: the canonical comparison in each degree, obtained
  from the right-Kan-extension adjunction.
* `Stacks.RelativeCech.baseChangeMap`: those components assembled into a map of complexes.

## Main results

* `Stacks.RelativeCech.baseChangeComponent_comm` is the compatibility of the components with
  the Čech differentials, which is what makes `baseChangeMap` a map of complexes.
* `Stacks.RelativeCech.isIso_baseChangeMap` is part (2): for horizontal equivalences the
  base-change morphism is an isomorphism of complexes of abelian presheaves.
* `Stacks.RelativeCech.nonempty_complexIso_of_natIso` is part (3): `2`-isomorphic
  `1`-morphisms have isomorphic relative Čech complexes.

## Implementation notes

`𝒦^•(f, F)` is the relative Čech complex of an abelian presheaf, `Stacks.RelativeCech.complex`.
The source defines it for a sheaf and extends it to presheaves, and the pullback maps of that
extension are what this proof uses; the statement therefore lives at the presheaf level and
nothing is sheafified. This is harmless: for a sheaf `F` every term `f_{n,*}f_n⁻¹F` is already
a sheaf, and along a `1`-morphism of categories fibred in groupoids the inverse image of
(pre)sheaves *is* restriction, by
`CategoryTheory.Functor.IsFibredOneMorphism.inverseImageCompSheafToPresheafIso`. That is how
`e⁻¹` is modelled here, both on the coefficients and on the complex.

A `1`-morphism over the base commutes with the structure functors on the nose, so the structure
functors of `U`, `Y` and `V` are `f ⋙ pX`, `e ⋙ pX` and `g ⋙ e ⋙ pX`; no transport along an
equality of functors is needed anywhere. A `2`-morphism over the base is a natural
transformation whose components lie over identities, which is `hα`; over a category fibred in
groupoids it is automatically invertible, so it is given as a natural isomorphism, and that
invertibility is what produces the comparison isomorphisms of the Čech nerve. `hα` already
forces `(h ⋙ f) ⋙ pX = (g ⋙ e) ⋙ pX`, so that equation is not assumed separately.

The five categories carry independent object and morphism universes. The only universe
constraint is that the coefficients be large enough for the right Kan extensions along both
Čech nerves, which is the displayed `max`; the summand `w` stays free, so no two universes are
forced equal.

## References

* [Stacks Project, Tag 06X9](https://stacks.math.columbia.edu/tag/06X9)
* [Stacks Project, Tag 06X8](https://stacks.math.columbia.edu/tag/06X8)
* [Stacks Project, Tag 06X5](https://stacks.math.columbia.edu/tag/06X5)
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

namespace Stacks.RelativeCech

universe uC uU uV uX uY vC vU vV vX vY w

section Square

variable {C : Type uC} {X : Type uX} {U : Type uU} {Y : Type uY} {V : Type uV}
  [Category.{vC} C] [Category.{vX} X] [Category.{vU} U] [Category.{vY} Y]
  [Category.{vV} V] (pX : X ⥤ C) (f : U ⥤ X) (e : Y ⥤ X) (g : V ⥤ Y) (h : V ⥤ U)
  (α : h ⋙ f ≅ g ⋙ e)
  (hα : ∀ v : V, pX.IsHomLift (𝟙 (pX.obj (f.obj (h.obj v)))) (α.hom.app v))

/-- The canonical degreewise comparison, obtained by the right-Kan-extension
adjunction from the counit on the source Čech nerve. -/
public noncomputable def baseChangeComponent
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) (n : ℕ) :
    e.op ⋙ term.{vU, vX, vC, uU, uX, uC, max uV uY vY w} pX f F n ⟶
      term.{vV, vY, vC, uV, uY, uC, max uU uX vX w}
        (e ⋙ pX) g (e.op ⋙ F) n :=
  let qX := Tuple.projection pX f n
  let qY := Tuple.projection (e ⋙ pX) g n
  let k := Cech.nerveMap pX (e ⋙ pX) f g h e α rfl hα n
  ((qY.op.ranAdjunction AddCommGrpCat.{max uU uX vX uV uY vY w}).homEquiv _ _)
    (by
      change (qY ⋙ e).op ⋙ term pX f F n ⟶ (qY ⋙ e).op ⋙ F
      exact Functor.whiskerLeft k.op (qX.op.ranCounit.app (qX.op ⋙ F)))

/-- The degreewise comparisons are compatible with the coface pullback maps. -/
private theorem baseChangeComponent_coface
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w})
    (n : ℕ) (i : Fin (n + 2)) :
    baseChangeComponent pX f e g h α hα F n ≫
        reindexMap.{vV, vY, vC, uV, uY, uC, max uU uX vX w}
          (e ⋙ pX) g (e.op ⋙ F) (SimplexCategory.δ i) =
      Functor.whiskerLeft e.op
        (reindexMap.{vU, vX, vC, uU, uX, uC, max uV uY vY w}
          pX f F (SimplexCategory.δ i)) ≫
        baseChangeComponent pX f e g h α hα F (n + 1) := by
  let qYp := Tuple.projection (e ⋙ pX) g (n + 1)
  have hb (m : ℕ) :
      Functor.whiskerLeft (Tuple.projection (e ⋙ pX) g m).op
            (baseChangeComponent pX f e g h α hα F m) ≫
          (Tuple.projection (e ⋙ pX) g m).op.ranCounit.app
            ((Tuple.projection (e ⋙ pX) g m).op ⋙ e.op ⋙ F) =
        Functor.whiskerLeft (Cech.nerveMap pX (e ⋙ pX) f g h e α rfl hα m).op
          ((Tuple.projection pX f m).op.ranCounit.app ((Tuple.projection pX f m).op ⋙ F)) :=
    (((Tuple.projection (e ⋙ pX) g m).op.ranAdjunction
        AddCommGrpCat.{max uU uX vX uV uY vY w}).homEquiv_counit
      (g := baseChangeComponent pX f e g h α hα F m)).symm.trans (Equiv.symm_apply_apply _ _)
  apply ((qYp.op.ranAdjunction AddCommGrpCat.{max uU uX vX uV uY vY w}).homEquiv
    _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change Functor.whiskerLeft qYp.op
        (baseChangeComponent pX f e g h α hα F n) ≫
      (Functor.whiskerLeft qYp.op
          (reindexMap.{vV, vY, vC, uV, uY, uC, max uU uX vX w}
            (e ⋙ pX) g (e.op ⋙ F) (SimplexCategory.δ i)) ≫
        qYp.op.ranCounit.app (qYp.op ⋙ e.op ⋙ F)) =
    Functor.whiskerLeft qYp.op
        (Functor.whiskerLeft e.op
          (reindexMap.{vU, vX, vC, uU, uX, uC, max uV uY vY w}
            pX f F (SimplexCategory.δ i))) ≫
      (Functor.whiskerLeft qYp.op
          (baseChangeComponent pX f e g h α hα F (n + 1)) ≫
        qYp.op.ranCounit.app (qYp.op ⋙ e.op ⋙ F))
  rw [reindexMap_fac.{vV, vY, vC, uV, uY, uC, max uU uX vX w}
      (p := e ⋙ pX) (f := g) (F := e.op ⋙ F) (m := n) (n := n + 1) (SimplexCategory.δ i),
    hb (n + 1)]
  let qX := Tuple.projection pX f n
  let qXp := Tuple.projection pX f (n + 1)
  let qY := Tuple.projection (e ⋙ pX) g n
  let rX := Tuple.reindex pX f (SimplexCategory.δ i).toOrderHom
  let rY := Tuple.reindex (e ⋙ pX) g (SimplexCategory.δ i).toOrderHom
  let kp := Cech.nerveMap pX (e ⋙ pX) f g h e α rfl hα (n + 1)
  have hleft : Functor.whiskerLeft qYp.op (baseChangeComponent pX f e g h α hα F n) =
      Functor.whiskerLeft rY.op
        (Functor.whiskerLeft qY.op (baseChangeComponent pX f e g h α hα F n)) := rfl
  have hmap :
      Functor.whiskerLeft qYp.op
          (Functor.whiskerLeft e.op
            (reindexMap.{vU, vX, vC, uU, uX, uC, max uV uY vY w}
              pX f F (SimplexCategory.δ i))) =
        Functor.whiskerLeft kp.op
          (Functor.whiskerLeft qXp.op
            (reindexMap.{vU, vX, vC, uU, uX, uC, max uV uY vY w}
              pX f F (SimplexCategory.δ i))) := rfl
  have hfacX :
      Functor.whiskerLeft qXp.op
          (reindexMap.{vU, vX, vC, uU, uX, uC, max uV uY vY w}
            pX f F (SimplexCategory.δ i)) ≫
        qXp.op.ranCounit.app (qXp.op ⋙ F) =
      Functor.whiskerLeft rX.op (qX.op.ranCounit.app (qX.op ⋙ F)) :=
    reindexMap_fac (p := pX) (f := f) (F := F) (SimplexCategory.δ i)
  rw [hleft, ← Functor.whiskerLeft_comp, hb n, hmap]
  exact (congrArg (Functor.whiskerLeft kp.op) hfacX.symm).trans
    (Functor.whiskerLeft_comp kp.op
      (Functor.whiskerLeft qXp.op
        (reindexMap.{vU, vX, vC, uU, uX, uC, max uV uY vY w} pX f F (SimplexCategory.δ i)))
      (qXp.op.ranCounit.app (qXp.op ⋙ F)))

/-- The induced `1`-morphism of relative Čech nerves is an equivalence when both horizontal
functors are. -/
private lemma nerveMap_isEquivalence [h.IsEquivalence] [e.IsEquivalence]
    (hpV : (g ⋙ e ⋙ pX).IsFiberedInGroupoids) (n : ℕ) :
    (Cech.nerveMap pX (e ⋙ pX) f g h e α rfl hα n).IsEquivalence where
  faithful := Cech.nerveMap_faithful pX (e ⋙ pX) f g h e α rfl hα n
  full := Cech.nerveMap_full pX (e ⋙ pX) f g h e α rfl hα n
  essSurj := Cech.nerveMap_essSurj pX (e ⋙ pX) f g h e α rfl hα hpV n

/-- Each degreewise comparison is an isomorphism when both horizontal functors are
equivalences: the source is then also a right Kan extension along the target projection. -/
private theorem baseChangeComponent_isIso
    [h.IsEquivalence] [e.IsEquivalence]
    (hpV : (g ⋙ e ⋙ pX).IsFiberedInGroupoids)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) (n : ℕ) :
    IsIso (baseChangeComponent pX f e g h α hα F n) := by
  let qX := Tuple.projection pX f n
  let qY := Tuple.projection (e ⋙ pX) g n
  let k := Cech.nerveMap pX (e ⋙ pX) f g h e α rfl hα n
  have : k.IsEquivalence := nerveMap_isEquivalence
    pX f e g h α hα hpV n
  let H : (Tuple pX f n)ᵒᵖ ⥤
      AddCommGrpCat.{max uU uX vX uV uY vY w} := qX.op ⋙ F
  let α₁ : qY.op ⋙ (e.op ⋙ qX.op.ran.obj H) ⟶ qY.op ⋙ e.op ⋙ F :=
    qY.op.whiskerLeft (Iso.refl (e.op ⋙ qX.op.ran.obj H)).inv ≫
      (qY.op.associator e.op (qX.op.ran.obj H)).inv ≫
      Functor.whiskerRight (Iso.refl (k.op ⋙ qX.op)).inv (qX.op.ran.obj H) ≫
        (k.op.associator qX.op (qX.op.ran.obj H)).hom ≫
          k.op.whiskerLeft (qX.op.ranCounit.app H) ≫
            (Iso.refl (qY.op ⋙ e.op ⋙ F)).inv
  have hkan₁ : (e.op ⋙ qX.op.ran.obj H).IsRightKanExtension α₁ :=
    (Functor.isRightKanExtension_iff_precomp_equivalence α₁
      (qX.op.ranCounit.app H) (G := k.op) (G' := e.op)
      (iso := Iso.refl _) (e := Iso.refl _) (e' := Iso.refl _)
      (h := rfl)).mp inferInstance
  have hα₁ : α₁ = Functor.whiskerLeft k.op (qX.op.ranCounit.app H) := by
    ext x
    simp [α₁, Functor.associator, Functor.whiskerRight_id',
      Functor.whiskerLeft_app, NatTrans.comp_app]
    rfl
  unfold baseChangeComponent
  dsimp
  rw [← hα₁]
  exact (Functor.isIso_ranAdjunction_homEquiv_iff
    (L := qY.op) (H := AddCommGrpCat.{max uU uX vX uV uY vY w}) α₁).2 hkan₁

/-- The canonical degreewise maps commute with the Čech differentials. -/
public theorem baseChangeComponent_comm
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) :
    let A := (((Functor.whiskeringLeft Yᵒᵖ Xᵒᵖ
      AddCommGrpCat.{max uU uX vX uV uY vY w}).obj e.op).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        (complex.{vU, vX, vC, uU, uX, uC, max uV uY vY w} pX f F)
    let B := complex.{vV, vY, vC, uV, uY, uC, max uU uX vX w}
      (e ⋙ pX) g (e.op ⋙ F)
    ∀ i j, (ComplexShape.up ℕ).Rel i j →
      baseChangeComponent pX f e g h α hα F i ≫ B.d i j =
        A.d i j ≫ baseChangeComponent pX f e g h α hα F j := by
  dsimp only
  rintro i _ rfl
  simp only [complex_X]
  change baseChangeComponent pX f e g h α hα F i ≫
      (complex (e ⋙ pX) g (e.op ⋙ F)).d i (i + 1) =
    ((Functor.whiskeringLeft Yᵒᵖ Xᵒᵖ
      AddCommGrpCat.{max uU uX vX uV uY vY w}).obj e.op).map
        ((complex pX f F).d i (i + 1)) ≫
      baseChangeComponent pX f e g h α hα F (i + 1)
  rw [complex_d.{vV, vY, vC, uV, uY, uC, max uU uX vX w}
        (p := e ⋙ pX) (f := g) (F := e.op ⋙ F) i,
      complex_d.{vU, vX, vC, uU, uX, uC, max uV uY vY w}
        (p := pX) (f := f) (F := F) i]
  simp only [complex_X, Functor.map_sum, Functor.map_zsmul,
    Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [baseChangeComponent_coface pX f e g h α hα F i k]
  rfl

/-- **Stacks 06X9, part (1).** The canonical comparison is assembled from the
right-Kan-extension adjunction in each Čech degree. -/
@[stacks 06X9 "part (1)"]
public noncomputable def baseChangeMap
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) :
    (((Functor.whiskeringLeft Yᵒᵖ Xᵒᵖ
      AddCommGrpCat.{max uU uX vX uV uY vY w}).obj e.op).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        (complex.{vU, vX, vC, uU, uX, uC, max uV uY vY w} pX f F) ⟶
      complex.{vV, vY, vC, uV, uY, uC, max uU uX vX w}
        (e ⋙ pX) g (e.op ⋙ F) where
  f n := baseChangeComponent pX f e g h α hα F n
  comm' := baseChangeComponent_comm pX f e g h α hα F

/-- **Stacks 06X9, part (2).** If the two horizontal 1-morphisms `h` and `e` of the
square are equivalences, then the base-change morphism of part (1) is an
isomorphism of complexes of abelian presheaves. -/
@[stacks 06X9 "part (2)"]
public theorem isIso_baseChangeMap
    [h.IsEquivalence] [e.IsEquivalence]
    (hpV : (g ⋙ e ⋙ pX).IsFiberedInGroupoids)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) :
    IsIso (baseChangeMap pX f e g h α hα F) := by
  have (n : ℕ) : IsIso ((baseChangeMap pX f e g h α hα F).f n) :=
    baseChangeComponent_isIso pX f e g h α hα hpV F n
  exact HomologicalComplex.Hom.isIso_of_components _

end Square

/-- **Stacks 06X9, part (3).** 2-isomorphic 1-morphisms `f, f' : 𝒰 ⟶ 𝒳` over the
base have isomorphic relative Čech complexes. -/
@[stacks 06X9 "part (3)"]
public theorem nonempty_complexIso_of_natIso
    {C : Type uC} {X : Type uX} {U : Type uU} [Category.{vC} C] [Category.{vX} X]
    [Category.{vU} U] (pX : X ⥤ C) (f f' : U ⥤ X) (β : f ≅ f')
    (hβ : ∀ u : U, pX.IsHomLift (𝟙 (pX.obj (f.obj u))) (β.hom.app u))
    (hpU' : (f' ⋙ pX).IsFiberedInGroupoids)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) :
    Nonempty (complex pX f F ≅ complex pX f' F) := by
  let α₀ : (𝟭 U) ⋙ f ≅ f' ⋙ (𝟭 X) :=
    Functor.leftUnitor f ≪≫ β ≪≫ (Functor.rightUnitor f').symm
  have hα₀ : ∀ u : U,
      pX.IsHomLift (𝟙 (pX.obj (f.obj ((𝟭 U).obj u)))) (α₀.hom.app u) :=
    fun u => by simpa [α₀] using hβ u
  have hpV₀ : (f' ⋙ (𝟭 X) ⋙ pX).IsFiberedInGroupoids := by
    simpa only [Functor.comp_id, Functor.id_comp] using hpU'
  let m := baseChangeMap pX f (𝟭 X) f' (𝟭 U) α₀ hα₀ F
  have : IsIso m := isIso_baseChangeMap pX f (𝟭 X) f' (𝟭 U) α₀ hα₀ hpV₀ F
  exact ⟨asIso m⟩

end Stacks.RelativeCech

end
