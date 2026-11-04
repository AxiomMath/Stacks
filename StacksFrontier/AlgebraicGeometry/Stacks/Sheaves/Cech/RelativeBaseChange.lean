module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeGeneralities
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# Base change for the relative Čech complex

For a `2`-fibre-product square of categories fibred in groupoids, the canonical base-change map
on relative Čech complexes of abelian presheaves is an isomorphism.

## Main definitions

* `Stacks.RelativeCech.squareNatIso`: the natural isomorphism of underlying functors supplied by
  a square of categories fibred in groupoids.

## Main results

* `Stacks.RelativeCech.isIso_baseChangeMap_of_isTwoFibreProduct`: the base-change map of
  `Stacks.RelativeCech.baseChangeMap` is an isomorphism of complexes of abelian presheaves.

## Implementation notes

The assertion is stated over an arbitrary base category; the case of interest is the big fppf
site over a scheme. The `2`-fibre-product condition is that the comparison functor to the
concrete fibre product over the base be an equivalence, the latter having among its objects
every vertical comparison isomorphism. Terminality among categories in a fixed universe does not
imply this equivalence when the fibres contain objects or morphisms in a larger universe, which
is why the hypothesis is stated as an equivalence.

The proof identifies the degreewise comparison with the base-change map of a `TwoSquare` of
right Kan extensions and shows that square to be Guitart exact: in each Čech degree the induced
functor on costructured arrows over an object of `Y` is an equivalence, which is exactly
finality of that functor.

## References

* [Stacks Project, Tag 06XC](https://stacks.math.columbia.edu/tag/06XC)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RelativeCech

universe vC vD uC uD w vX vU vY vV uX uU uY uV

variable {C : Type uC} [Category.{vC} C]
  {X U Y : CatFiberedInGroupoids.{vC, vD, uC, uD} C}
  (f : U ⟶ X) (e : Y ⟶ X)
  (P : Bicategory.TwoCommSq f e)

section SquareNatIso

/-- The natural isomorphism of underlying functors supplied by a square of
categories fibred in groupoids. -/
public def squareNatIso :
    P.fst.hom.toFunctor ⋙ f.hom.toFunctor ≅
      P.snd.hom.toFunctor ⋙ e.hom.toFunctor where
  hom := P.iso.hom.hom.toNatTrans
  inv := P.iso.inv.hom.toNatTrans
  hom_inv_id := congrArg (fun k => k.hom.toNatTrans) P.iso.hom_inv_id
  inv_hom_id := congrArg (fun k => k.hom.toNatTrans) P.iso.inv_hom_id

end SquareNatIso

open Functor

/-- In a category fibred in groupoids, a morphism of `Y` over a fixed object is determined,
uniquely and existentially, by its image in `X` together with its compatibility with the
structure morphisms to that object. -/
private theorem over_map_bijective
    {X : Type uX} {Y : Type uY} [Category.{vX} X] [Category.{vY} Y]
    (p : X ⥤ C) (e : Y ⥤ X)
    (hp : p.IsFiberedInGroupoids) (he : (e ⋙ p).IsFiberedInGroupoids)
    {y y₁ y₂ : Y} (β : y₁ ⟶ y) (γ : y₂ ⟶ y)
    (a : e.obj y₁ ⟶ e.obj y₂) (ha : a ≫ e.map γ = e.map β) :
    ∃! b : y₁ ⟶ y₂, e.map b = a ∧ b ≫ γ = β := by
  obtain ⟨b, ⟨hb, hbγ⟩, huniq⟩ := he.unique_lift γ β (p.map a)
    (by simp only [Functor.comp_map, ← Functor.map_comp, ha])
  have hba : e.map b = a := by
    obtain ⟨_, -, hu⟩ := hp.unique_lift (e.map γ) (e.map β) (p.map a)
      (by rw [← p.map_comp, ha])
    exact (hu _ ⟨hb, by rw [← e.map_comp, hbγ]⟩).trans (hu _ ⟨rfl, ha⟩).symm
  exact ⟨b, ⟨hba, hbγ⟩, fun b' hb' => huniq b' ⟨by simp [hb'.1], hb'.2⟩⟩

/-- A morphism `x ⟶ e y` in `X` factors, after replacing `y` by an object over it, as a vertical
isomorphism followed by the image of a morphism of `Y`. -/
private theorem over_obj_lift
    {X : Type uX} {Y : Type uY} [Category.{vX} X] [Category.{vY} Y]
    (p : X ⥤ C) (e : Y ⥤ X)
    (hp : p.IsFiberedInGroupoids) (he : (e ⋙ p).IsFiberedInGroupoids)
    {x : X} {y : Y} (a : x ⟶ e.obj y) :
    ∃ (y' : Y) (β : y' ⟶ y) (i : x ≅ e.obj y'),
      p.IsHomLift (𝟙 (p.obj x)) i.hom ∧ i.hom ≫ e.map β = a := by
  obtain ⟨y', β, hβ⟩ := he.exists_lift (p.map a) y rfl
  have hβ' : p.IsHomLift (p.map a) (e.map β) :=
    (Functor.isHomLift_comp_iff e p _ _).mp hβ
  have := hp.isStronglyCartesian_homLift (p.map a) (e.map β)
  have := hp.isStronglyCartesian a
  exact ⟨y', β, IsCartesian.domainUniqueUpToIso p (p.map a) (e.map β) a,
    IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _, IsCartesian.fac p (p.map a) (e.map β) a⟩

section Comparison

variable {X : Type uX} {U : Type uU} {Y : Type uY} {V : Type uV}
  [Category.{vX} X] [Category.{vU} U] [Category.{vY} Y] [Category.{vV} V]
  (p : X ⥤ C) (f : U ⥤ X) (e : Y ⥤ X) (g : V ⥤ Y) (h : V ⥤ U)
  (α : h ⋙ f ≅ g ⋙ e)
  (hα : ∀ v, p.IsHomLift (𝟙 (p.obj (f.obj (h.obj v)))) (α.hom.app v))
  (hh : h ⋙ f ⋙ p = g ⋙ e ⋙ p)

/-- The structure isomorphism `α` is vertical over the base. -/
private theorem isHomLift_app_hom
    (hα : ∀ v, p.IsHomLift (𝟙 (p.obj (f.obj (h.obj v)))) (α.hom.app v))
    (hh : h ⋙ f ⋙ p = g ⋙ e ⋙ p) (v : V) :
    p.IsHomLift (𝟙 ((g ⋙ e ⋙ p).obj v)) (α.hom.app v) := by
  rw [← Functor.congr_obj hh v]
  exact hα v

/-- The comparison functor from `V` to the concrete `2`-fibre product of `f` and `e` over the
base, attached to the given `2`-commutative square. -/
private abbrev twoFibreComparison :=
  TwoFibreProductOver.lift (f ⋙ p) (e ⋙ p) p f e (g ⋙ e ⋙ p) h g hh rfl α
    (isHomLift_app_hom p f e g h α hα hh)

/-- When the comparison functor is full, a compatible pair of morphisms of `U` and `Y` comes
from a morphism of `V`. -/
private theorem comparison_lift_hom
    [(twoFibreComparison p f e g h α hα hh).Full]
    {v v' : V} (a : h.obj v ⟶ h.obj v') (b : g.obj v ⟶ g.obj v')
    (hab : f.map a ≫ α.hom.app v' = α.hom.app v ≫ e.map b) :
    ∃ t : v ⟶ v', h.map t = a ∧ g.map t = b := by
  let K := twoFibreComparison p f e g h α hα hh
  have hmap (v : V) : p.map (α.hom.app v) = eqToHom (Functor.congr_obj hh v) := by
    have := hα v
    simpa using IsHomLift.fac' p (𝟙 (p.obj (f.obj (h.obj v)))) (α.hom.app v)
  let P : V → TwoFibreProductOver (f ⋙ p) (e ⋙ p) p f e := fun v =>
    { base := (g ⋙ e ⋙ p).obj v
      x := h.obj v
      y := g.obj v
      hx := Functor.congr_obj hh v
      hy := rfl
      iso := α.app v
      vertical := isHomLift_app_hom p f e g h α hα hh v }
  let ab : P v ⟶ P v' := TwoFibreProductOver.Hom.mk' a b (by
    have heq := congrArg (fun t => p.map t) hab
    simp only [Functor.map_comp, hmap] at heq
    simp only [P, Functor.comp_obj, Functor.comp_map, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    rw [heq]
    simp) hab
  have hK := K.map_preimage (ab : K.obj v ⟶ K.obj v')
  exact ⟨_, congrArg TwoFibreProductOver.Hom.a hK, congrArg TwoFibreProductOver.Hom.b hK⟩

/-- When the comparison functor is faithful, a morphism of `V` is determined by its images in
`U` and in `Y`. -/
private theorem comparison_hom_ext
    [(twoFibreComparison p f e g h α hα hh).Faithful]
    {v v' : V} {a b : v ⟶ v'} (ha : h.map a = h.map b) (hb : g.map a = g.map b) : a = b :=
  (twoFibreComparison p f e g h α hα hh).map_injective (TwoFibreProductOver.Hom.ext' ha hb)

/-- When the comparison functor is an equivalence, a vertical isomorphism `f u ≅ e y` is induced
by an object of `V` together with isomorphisms to `u` and to `y`. -/
private theorem comparison_lift_iso
    [(twoFibreComparison p f e g h α hα hh).IsEquivalence]
    (hp : p.IsFiberedInGroupoids) (hf : (f ⋙ p).IsFiberedInGroupoids)
    (he : (e ⋙ p).IsFiberedInGroupoids) (hg : (g ⋙ e ⋙ p).IsFiberedInGroupoids)
    {u : U} {y : Y} (i : f.obj u ≅ e.obj y)
    (hi : p.IsHomLift (𝟙 (p.obj (e.obj y))) i.hom) :
    ∃ (v : V) (a : h.obj v ≅ u) (b : g.obj v ≅ y),
      (e ⋙ p).IsHomLift (𝟙 (p.obj (e.obj y))) b.hom ∧
        f.map a.hom ≫ i.hom = α.hom.app v ≫ e.map b.hom := by
  let K := twoFibreComparison p f e g h α hα hh
  let q := TwoFibreProductOver.structureFunctor (f ⋙ p) (e ⋙ p) p f e
  let z : TwoFibreProductOver (f ⋙ p) (e ⋙ p) p f e :=
    ⟨p.obj (e.obj y), u, y, @IsHomLift.domain_eq _ _ _ _ p _ _ _ _ _ _ hi,
      rfl, i, hi⟩
  obtain ⟨v, hv, j, hj⟩ := Functor.quasiInverse_choice (g ⋙ e ⋙ p) q hg
    (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hf he hp rfl rfl)
    K (TwoFibreProductOver.lift_comp_structureFunctor ..) inferInstance z
  let a := (TwoFibreProductOver.fst (f ⋙ p) (e ⋙ p) p f e).mapIso j.symm
  let b := (TwoFibreProductOver.snd (f ⋙ p) (e ⋙ p) p f e).mapIso j.symm
  refine ⟨v, a, b, ?_, j.inv.w⟩
  apply (Functor.isHomLift_map_iff_of_comp_eq q (e ⋙ p)
    (TwoFibreProductOver.snd (f ⋙ p) (e ⋙ p) p f e)
    (TwoFibreProductOver.snd_comp_eq ..) _ j.inv).mpr
  have := hj
  exact inferInstanceAs (q.IsHomLift (𝟙 (q.obj z)) j.inv)

/-- In each Čech degree, the functor on costructured arrows over an object `y` of `Y` induced by
the `1`-morphism of Čech nerves. -/
private def nerveOverMap (n : ℕ) (y : Y) :
    CostructuredArrow (Tuple.projection (e ⋙ p) g n) y ⥤
      CostructuredArrow (Tuple.projection p f n) (e.obj y) where
  obj a := CostructuredArrow.mk
    (Y := (Cech.nerveMap p (e ⋙ p) f g h e α rfl hα n).obj a.left) (e.map a.hom)
  map {a b} t := CostructuredArrow.homMk
    ((Cech.nerveMap p (e ⋙ p) f g h e α rfl hα n).map t.left)
    (by
      change e.map t.left.target ≫ e.map b.hom = e.map a.hom
      simpa only [Tuple.projection, ← e.map_comp] using
        congrArg e.map (CostructuredArrow.w t))
  map_id a := by
    ext
    exact (Cech.nerveMap p (e ⋙ p) f g h e α rfl hα n).map_id _
  map_comp t t' := by
    ext
    exact (Cech.nerveMap p (e ⋙ p) f g h e α rfl hα n).map_comp _ _

/-- The induced functor on costructured arrows is full. -/
private theorem nerveOverMap_full
    [(twoFibreComparison p f e g h α hα hh).Full]
    (hp : p.IsFiberedInGroupoids) (he : (e ⋙ p).IsFiberedInGroupoids)
    (n : ℕ) (y : Y) : (nerveOverMap p f e g h α hα n y).Full := by
  classical
  constructor
  intro a b t
  obtain ⟨δ, ⟨hδ, hδb⟩, _⟩ := over_map_bijective p e hp he a.hom b.hom
    t.left.target (CostructuredArrow.w t)
  have hs (i : Fin (n + 1)) : ∃ s : a.left.source i ⟶ b.left.source i,
      h.map s = t.left.source i ∧
        g.map s = (a.left.comparison i).hom ≫ δ ≫ (b.left.comparison i).inv := by
    apply comparison_lift_hom p f e g h α hα hh
    have ht := t.left.comparison_naturality i
    dsimp [nerveOverMap, Cech.nerveMap] at ht
    simp only [Functor.map_comp]
    rw [← hδ] at ht
    rw [← cancel_mono (e.map (b.left.comparison i).hom)]
    simpa [Category.assoc] using ht
  choose s hs hg using hs
  let z : a.left ⟶ b.left :=
    { target := δ
      source := s
      comparison_naturality := fun i => by simp [hg] }
  exact ⟨CostructuredArrow.homMk z hδb,
    CostructuredArrow.hom_ext _ _ (Cech.tupleHom_ext hδ (funext hs))⟩

/-- The induced functor on costructured arrows is faithful. -/
private theorem nerveOverMap_faithful
    [(twoFibreComparison p f e g h α hα hh).Faithful]
    (hp : p.IsFiberedInGroupoids) (he : (e ⋙ p).IsFiberedInGroupoids)
    (n : ℕ) (y : Y) : (nerveOverMap p f e g h α hα n y).Faithful := by
  constructor
  intro a b t t' ht
  have ht₁ := congrArg (fun z => z.left.target) ht
  have ht₂ := congrArg (fun z => z.left.source) ht
  obtain ⟨δ, hδ, hu⟩ := over_map_bijective p e hp he a.hom b.hom
    (e.map t.left.target) (by
      simpa only [Tuple.projection, Functor.map_comp] using
        congrArg e.map (CostructuredArrow.w t))
  have htarget : t.left.target = t'.left.target :=
    (hu _ ⟨rfl, CostructuredArrow.w t⟩).trans
      (hu _ ⟨ht₁.symm, CostructuredArrow.w t'⟩).symm
  apply CostructuredArrow.hom_ext
  apply Cech.tupleHom_ext htarget
  funext i
  apply comparison_hom_ext p f e g h α hα hh (congrFun ht₂ i)
  rw [← cancel_mono (b.left.comparison i).hom,
    t.left.comparison_naturality, t'.left.comparison_naturality, htarget]

/-- The induced functor on costructured arrows is essentially surjective. -/
private theorem nerveOverMap_essSurj
    [(twoFibreComparison p f e g h α hα hh).IsEquivalence]
    (hp : p.IsFiberedInGroupoids) (hf : (f ⋙ p).IsFiberedInGroupoids)
    (he : (e ⋙ p).IsFiberedInGroupoids) (hg : (g ⋙ e ⋙ p).IsFiberedInGroupoids)
    (n : ℕ) (y : Y) : (nerveOverMap p f e g h α hα n y).EssSurj := by
  classical
  constructor
  intro a
  obtain ⟨y', β, i, hi, ha⟩ := over_obj_lift p e hp he a.hom
  change p.IsHomLift (𝟙 (p.obj a.left.target)) i.hom at hi
  have hb (j : Fin (n + 1)) : ∃ (v : V) (s : h.obj v ≅ a.left.source j)
      (t : g.obj v ≅ y'),
      (e ⋙ p).IsHomLift (𝟙 (p.obj (e.obj y'))) t.hom ∧
      f.map s.hom ≫ ((a.left.comparison j) ≪≫ i).hom =
        α.hom.app v ≫ e.map t.hom := by
    apply comparison_lift_iso p f e g h α hα hh hp hf he hg
    have := hi
    have := a.left.comparison_lift j
    have hbase := IsHomLift.codomain_eq p (𝟙 (p.obj a.left.target)) i.hom
    rw [hbase]
    exact IsHomLift.comp_lift_id_left' p (p.obj a.left.target)
      (a.left.comparison j).hom (𝟙 (p.obj a.left.target)) i.hom
  choose v s t ht hs using hb
  let b : Tuple (e ⋙ p) g n := ⟨y', v, t, ht⟩
  let z : CostructuredArrow (Tuple.projection (e ⋙ p) g n) y :=
    CostructuredArrow.mk (Y := b) β
  refine ⟨z, ⟨CostructuredArrow.isoMk (Cech.tupleIso i.symm s ?_) ?_⟩⟩
  · intro j
    rw [← cancel_mono i.hom]
    simpa [nerveOverMap, Cech.nerveMap, z, b, Category.assoc] using hs j
  · show i.inv ≫ a.hom = e.map β
    rw [← ha]
    simp

/-- The `2`-square of opposite categories, with identity `2`-cell, whose right-Kan-extension
base-change map is the degreewise comparison of relative Čech complexes. -/
private def baseChangeSquare (n : ℕ) :
    TwoSquare (Tuple.projection (e ⋙ p) g n).op
      (Cech.nerveMap p (e ⋙ p) f g h e α rfl hα n).op
      e.op (Tuple.projection p f n).op :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

/-- For a `2`-fibre-product square the base-change `2`-square is Guitart exact: in each Čech
degree the induced functor on costructured arrows is an equivalence, hence final. -/
private theorem baseChangeSquare_exact
    [(twoFibreComparison p f e g h α hα hh).IsEquivalence]
    (hp : p.IsFiberedInGroupoids) (hf : (f ⋙ p).IsFiberedInGroupoids)
    (he : (e ⋙ p).IsFiberedInGroupoids) (hg : (g ⋙ e ⋙ p).IsFiberedInGroupoids)
    (n : ℕ) : (baseChangeSquare p f e g h α hα n).GuitartExact := by
  let sq : TwoSquare (Cech.nerveMap p (e ⋙ p) f g h e α rfl hα n)
      (Tuple.projection (e ⋙ p) g n) (Tuple.projection p f n) e :=
    TwoSquare.mk _ _ _ _ (𝟙 _)
  have hsq : sq.GuitartExact := by
    rw [TwoSquare.guitartExact_iff_final]
    intro y
    have := nerveOverMap_full p f e g h α hα hh hp he n y
    have := nerveOverMap_faithful p f e g h α hα hh hp he n y
    have := nerveOverMap_essSurj p f e g h α hα hh hp hf he hg n y
    have : (nerveOverMap p f e g h α hα n y).IsEquivalence := .mk
    apply Functor.final_of_natIso (F := nerveOverMap p f e g h α hα n y)
    refine NatIso.ofComponents (fun a => CostructuredArrow.isoMk (Iso.refl _) ?_) ?_
    · simp [sq, nerveOverMap, TwoSquare.costructuredArrowRightwards, Tuple.projection,
        Cech.nerveMap, CostructuredArrow.post]
    · intro a b t
      apply CostructuredArrow.hom_ext
      simp only [Tuple.projection, nerveOverMap, Cech.nerveMap, comp_obj,
        CostructuredArrow.mk_left, TwoSquare.costructuredArrowRightwards,
        CostructuredArrow.post, CostructuredArrow.pre_obj_left, CostructuredArrow.comp_left,
        CostructuredArrow.isoMk_hom_left, Iso.refl_hom, Category.comp_id, Functor.comp_map,
        CostructuredArrow.pre_map_left, Category.id_comp]
      rfl
  exact inferInstanceAs sq.op.GuitartExact

/-- Guitart exactness of the base-change `2`-square makes the degreewise comparison of relative
Čech complexes an isomorphism. -/
private theorem isIso_baseChangeComponent_of_guitartExact
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) (n : ℕ)
    [(baseChangeSquare p f e g h α hα n).GuitartExact] :
    IsIso (baseChangeComponent p f e g h α hα F n) := by
  let sq := baseChangeSquare p f e g h α hα n
  have heq : baseChangeComponent p f e g h α hα F n =
      sq.ranBaseChange.app ((Tuple.projection p f n).op ⋙ F) := by
    dsimp [baseChangeComponent, TwoSquare.ranBaseChange,
      sq, baseChangeSquare, Functor.RightExtension.compTwoSquare]
    congr 1
    simp only [Cech.nerveMap, Tuple.projection, Functor.associator]
    ext a
    simp only [comp_obj, op_obj, id_eq, whiskerLeft_app, whiskerRight_id', Category.id_comp,
      NatTrans.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
    rfl
  rw [heq]
  have : sq.GuitartExact := inferInstanceAs
    (baseChangeSquare p f e g h α hα n).GuitartExact
  apply TwoSquare.isIso_ranBaseChange_app

end Comparison

/-- **Stacks 06XC.** Base change along a 2-fibre-product square induces an
isomorphism of relative Čech complexes of abelian presheaves. The comparison
with the concrete 2-fibre product is required to be an equivalence, including
when its category of objects lives in a larger universe. -/
@[stacks 06XC]
public theorem isIso_baseChangeMap_of_isTwoFibreProduct
    {X₀ : Type uX} {U₀ : Type uU} {Y₀ : Type uY} {V₀ : Type uV}
    [Category.{vX} X₀] [Category.{vU} U₀]
    [Category.{vY} Y₀] [Category.{vV} V₀]
    (pX : X₀ ⥤ C) (pU : U₀ ⥤ C) (pY : Y₀ ⥤ C) (pV : V₀ ⥤ C)
    (f₀ : U₀ ⥤ X₀) (e₀ : Y₀ ⥤ X₀) (g₀ : V₀ ⥤ Y₀) (h₀ : V₀ ⥤ U₀)
    (hf : f₀ ⋙ pX = pU) (he : e₀ ⋙ pX = pY)
    (hg : g₀ ⋙ pY = pV) (hh : h₀ ⋙ pU = pV)
    (α : h₀ ⋙ f₀ ≅ g₀ ⋙ e₀)
    (hα : ∀ v : V₀, pX.IsHomLift
      (𝟙 (pX.obj (f₀.obj (h₀.obj v)))) (α.hom.app v))
    (hpX : pX.IsFiberedInGroupoids) (hpU : pU.IsFiberedInGroupoids)
    (hpY : pY.IsFiberedInGroupoids) (hpV : pV.IsFiberedInGroupoids)
    (hP : (TwoFibreProductOver.lift pU pY pX f₀ e₀ pV h₀ g₀
      hh hg α (by
        intro v
        have hv : pX.obj (f₀.obj (h₀.obj v)) = pV.obj v := by
          calc
            _ = pU.obj (h₀.obj v) := Functor.congr_obj hf _
            _ = pV.obj v := Functor.congr_obj hh _
        rw [← hv]
        exact hα v)).IsEquivalence)
    (F : X₀ᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) :
    IsIso (baseChangeMap pX f₀ e₀ g₀ h₀ α hα F) := by
  cases hf
  cases he
  cases hg
  have : (twoFibreComparison pX f₀ e₀ g₀ h₀ α hα hh).IsEquivalence := hP
  refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ ?_
  intro n
  have := baseChangeSquare_exact pX f₀ e₀ g₀ h₀ α hα hh hpX hpU hpY hpV n
  exact isIso_baseChangeComponent_of_guitartExact pX f₀ e₀ g₀ h₀ α hα F n

end Stacks.RelativeCech

end
